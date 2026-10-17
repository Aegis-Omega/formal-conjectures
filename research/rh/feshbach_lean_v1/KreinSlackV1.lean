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
import RHKreinGenuineCertificateV1
import RHKreinHatAtV1

/-!
# Krein certificate with slack (the Krein step of the Feshbach certificates)

`feshbach_arb_v1` certifies in Arb that `W (S − m) + Ĥ + W s̄ ≥ 0` on the real line, with `Ĥ` a
sum of genuine hats supported in `|u| ≥ L` and `s̄` a step function, and concludes
`Q(G) ≥ m ‖G‖² − ⟨G, T G⟩` (`T` = multiplication by `s̄`). Its receipt lists the hat pairing as
not linked to Lean. Here the existing genuine-certificate pairing
(`RHKreinGenuineCertificateV1.real_angular_krein_pairing`) is combined with a slack term:

* `actual_margin_with_slack`, `zero_quadratic_margin_with_slack`: the weighted transfer of
  `RHKreinCertificateTransferV1` with an extra slack `s`;
* `zero_quadratic_margin_with_slack_from_genuine_certificate`: the same with a genuine `H`;
* `zero_quadratic_margin_with_slack_of_hats`: `H = ∑ cₖ hatAt uₖ`, with the certificate stated in
  the closed form `(2/50) sinc(t/100)² cos(t uₖ)` that the Arb verifier evaluates.

The symbol is the existing one (`2r < log 3`, prime 2 only), so this covers `L < log 3`.
-/

open MeasureTheory Complex FourierTransform Set
set_option autoImplicit false
noncomputable section

namespace AEGIS.KreinSlackV1

open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHKreinPrimeSymbolV1
open AEGIS.RHKreinCertificateTransferV1
open AEGIS.RHKreinFourierFactorV1
open AEGIS.RHKreinGenuineCertificateV1
open AEGIS.RHKreinHatAtV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilDisjointEnergyV2

/-- Weighted transfer with slack: `W (symbol − m + s) + C ≥ 0` and a zero-cost correction give
`Re(arithmetic side) ≤ −m E + (1/4π) ∫ s · M`. -/
theorem actual_margin_with_slack
    (g : WeilCompactSmoothGV1) (r a m : ℝ)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3)
    (ρ C s : ℝ → ℝ)
    (hρ : ∀ t : ℝ, 0 ≤ ρ t)
    (hmass : ∀ t : ℝ, criticalSpectralMass g t = (t ^ 2 + 1 / 4) ^ 2 * ρ t)
    (hCint : Integrable (fun t : ℝ => C t * ρ t))
    (hCzero : (∫ t : ℝ, C t * ρ t) = 0)
    (hsint : Integrable (fun t : ℝ => s t * criticalSpectralMass g t))
    (hcert : ∀ t : ℝ, 0 ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - m + s t) + C t) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤
      -m * energy g.1 + (1 / (4 * Real.pi)) * ∫ t : ℝ, s t * criticalSpectralMass g t := by
  have hS := symbol_mass_integrable g
  have hM := (criticalSpectralMass_integrable g).const_mul m
  have hSM : Integrable (fun t : ℝ =>
      symbol t * criticalSpectralMass g t - m * criticalSpectralMass g t) := hS.sub hM
  have hD : Integrable (fun t : ℝ =>
      symbol t * criticalSpectralMass g t - m * criticalSpectralMass g t +
        s t * criticalSpectralMass g t) := hSM.add hsint
  have hnonneg : 0 ≤ ∫ t : ℝ,
      (symbol t * criticalSpectralMass g t - m * criticalSpectralMass g t +
        s t * criticalSpectralMass g t) + C t * ρ t := by
    apply integral_nonneg
    intro t
    calc
      0 ≤ ((t ^ 2 + 1 / 4) ^ 2 * (symbol t - m + s t) + C t) * ρ t :=
        mul_nonneg (hcert t) (hρ t)
      _ = _ := by
        dsimp only
        rw [hmass]
        ring
  rw [integral_add hD hCint, hCzero, add_zero, integral_add hSM hsint,
    integral_sub hS hM, integral_const_mul] at hnonneg
  rw [actual_arithmetic_real_eq_symbol_integral g r a hw hr, energy_eq_mass_integral]
  have hK : 0 ≤ (1 / (4 * Real.pi) : ℝ) := by positivity
  have hbound := mul_nonneg hK hnonneg
  nlinarith

/-- Zero-quadratic form of `actual_margin_with_slack`. -/
theorem zero_quadratic_margin_with_slack
    (g : WeilCompactSmoothGV1) (r a m : ℝ)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3)
    (hm : WeilMomentConditionsV1 g)
    (ρ C s : ℝ → ℝ)
    (hρ : ∀ t : ℝ, 0 ≤ ρ t)
    (hmass : ∀ t : ℝ, criticalSpectralMass g t = (t ^ 2 + 1 / 4) ^ 2 * ρ t)
    (hCint : Integrable (fun t : ℝ => C t * ρ t))
    (hCzero : (∫ t : ℝ, C t * ρ t) = 0)
    (hsint : Integrable (fun t : ℝ => s t * criticalSpectralMass g t))
    (hcert : ∀ t : ℝ, 0 ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - m + s t) + C t) :
    m * energy g.1 - (1 / (4 * Real.pi)) * ∫ t : ℝ, s t * criticalSpectralMass g t ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have h := actual_margin_with_slack g r a m hw hr ρ C s hρ hmass hCint hCzero hsint hcert
  rw [AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10 g hm,
    Complex.neg_re] at h
  linarith

/-- Genuine certificate with slack: the correction `H`, supported in `|u| ≥ 2r`, pairs to zero by
`real_angular_krein_pairing`. -/
theorem zero_quadratic_margin_with_slack_from_genuine_certificate
    (g : WeilCompactSmoothGV1) (r a m : ℝ) (hr0 : 0 ≤ r)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3)
    (hm : WeilMomentConditionsV1 g)
    (H : ℝ → ℂ) (hHc : Continuous H) (hH : Integrable H) (hFH : Integrable (𝓕 H))
    (hHs : ∀ u : ℝ, |u| < 2 * r → H u = 0)
    (s : ℝ → ℝ) (hsint : Integrable (fun t : ℝ => s t * criticalSpectralMass g t))
    (hcert : ∀ t : ℝ, 0 ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - m + s t) +
      (𝓕 H (-t / (2 * Real.pi))).re) :
    m * energy g.1 - (1 / (4 * Real.pi)) * ∫ t : ℝ, s t * criticalSpectralMass g t ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  obtain ⟨χ, hc, hs, hi, hf⟩ :=
    actual_packet_fourier_factor g (a - r) (a + r) (by linarith) hw hm
  let χn : ℝ → ℂ := fun x => χ (-x)
  let ρ : ℝ → ℝ := fun t => Complex.normSq (𝓕 χ (-t / (2 * Real.pi))) +
    Complex.normSq (𝓕 χn (-t / (2 * Real.pi)))
  let C : ℝ → ℝ := fun t => (𝓕 H (-t / (2 * Real.pi))).re
  have hχs : ∀ y, χ y ≠ 0 → y ∈ Ioo (a - r) (a + r) :=
    AEGIS.RHKreinFactorV13.ne_zero_mem_Ioo χ hc.continuous (a - r) (a + r) hs
  have hχns : ∀ y, χn y ≠ 0 → y ∈ Ioo (-(a + r)) (-(a - r)) := by
    intro y hy
    have h := hχs (-y) hy
    constructor <;> linarith [h.1, h.2]
  have hχni : Integrable χn := hi.comp_neg
  have hfirst := real_angular_krein_pairing χ (a - r) (a + r) hi hχs
    H hHc hH hFH (fun u hu => hHs u (by linarith))
  have hsecond := real_angular_krein_pairing χn (-(a + r)) (-(a - r)) hχni hχns
    H hHc hH hFH (fun u hu => hHs u (by linarith))
  have hρ : ∀ t : ℝ, 0 ≤ ρ t := by
    intro t
    exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hmass : ∀ t : ℝ, criticalSpectralMass g t = (t ^ 2 + 1 / 4) ^ 2 * ρ t := by
    intro t
    unfold criticalSpectralMass
    rw [hf t, hf (-t)]
    dsimp [ρ, χn]
    rw [fourier_reflection]
    have he : -(-t / (2 * Real.pi)) = -(-t) / (2 * Real.pi) := by ring
    rw [he]
    ring
  have hsplit : ∀ t : ℝ, C t * ρ t =
      (𝓕 H (-t / (2 * Real.pi))).re * Complex.normSq (𝓕 χ (-t / (2 * Real.pi))) +
      (𝓕 H (-t / (2 * Real.pi))).re * Complex.normSq (𝓕 χn (-t / (2 * Real.pi))) := by
    intro t
    dsimp [C, ρ]
    ring
  have hCi : Integrable (fun t : ℝ => C t * ρ t) :=
    (hfirst.1.add hsecond.1).congr (Filter.Eventually.of_forall fun t => by
      change (𝓕 H (-t / (2 * Real.pi))).re *
          Complex.normSq (𝓕 χ (-t / (2 * Real.pi))) +
        (𝓕 H (-t / (2 * Real.pi))).re *
          Complex.normSq (𝓕 χn (-t / (2 * Real.pi))) = C t * ρ t
      exact (hsplit t).symm)
  have hCz : (∫ t : ℝ, C t * ρ t) = 0 := by
    simp_rw [hsplit]
    rw [integral_add hfirst.1 hsecond.1, hfirst.2, hsecond.2, add_zero]
  exact zero_quadratic_margin_with_slack g r a m hw hr hm ρ C s hρ hmass hCi hCz hsint hcert

/-- Fourier transform of a finite sum of integrable functions. -/
theorem fourier_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, Integrable (f i)) (ξ : ℝ) :
    𝓕 (fun x => ∑ i ∈ S, f i x) ξ = ∑ i ∈ S, 𝓕 (f i) ξ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    rw [fourier_add' (f a) (fun x => ∑ i ∈ S, f i x) (hf a (Finset.mem_insert_self a S))
      (integrable_finsetSum S fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **Hat certificate with slack.** For hats at centres `uₖ ≥ 2r + 1/50` with real coefficients
`cₖ`, the pointwise inequality in the closed form evaluated by the Arb verifier gives
`m E(g) − (1/4π) ∫ s · M_g ≤` the zero quadratic. -/
theorem zero_quadratic_margin_with_slack_of_hats {n : ℕ}
    (g : WeilCompactSmoothGV1) (r a m : ℝ) (hr0 : 0 ≤ r)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3)
    (hm : WeilMomentConditionsV1 g)
    (u c : Fin n → ℝ) (hu : ∀ k, 2 * r + 1 / 50 ≤ u k)
    (s : ℝ → ℝ) (hsint : Integrable (fun t : ℝ => s t * criticalSpectralMass g t))
    (hcert : ∀ t : ℝ, 0 ≤ (t ^ 2 + 1 / 4) ^ 2 * (symbol t - m + s t) +
      ∑ k, c k * ((2 / 50) * Real.sinc (t / 100) ^ 2 * Real.cos (t * u k))) :
    m * energy g.1 - (1 / (4 * Real.pi)) * ∫ t : ℝ, s t * criticalSpectralMass g t ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  let col : Fin n → ℝ → ℂ := fun k x => ((c k : ℝ) : ℂ) * hatAt (u k) x
  have hcol : ∀ k ∈ (Finset.univ : Finset (Fin n)), Integrable (col k) :=
    fun k _ => (hatAt_integrable (u k)).const_mul _
  let H : ℝ → ℂ := fun x => ∑ k, col k x
  have hF : ∀ ξ, 𝓕 H ξ = ∑ k, ((c k : ℝ) : ℂ) * 𝓕 (hatAt (u k)) ξ := by
    intro ξ
    rw [fourier_finset_sum Finset.univ col hcol ξ]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact fourier_const_mul' (hatAt (u k)) _ ξ
  refine zero_quadratic_margin_with_slack_from_genuine_certificate g r a m hr0 hw hr hm H
    (continuous_finsetSum _ fun k _ => continuous_const.mul (hatAt_continuous (u k)))
    (integrable_finsetSum _ hcol) ?_ ?_ s hsint ?_
  · refine (integrable_finsetSum Finset.univ fun k _ =>
      (hatAt_fourier_integrable (u k)).const_mul ((c k : ℝ) : ℂ)).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    exact (hF ξ).symm
  · intro x hx
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [col]
    rw [hatAt_zero (u k) (by linarith [hu k]), mul_zero]
  · intro t
    have he : (𝓕 H (-t / (2 * Real.pi))).re =
        ∑ k, c k * ((2 / 50) * Real.sinc (t / 100) ^ 2 * Real.cos (t * u k)) := by
      rw [hF, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.re_ofReal_mul, hatAt_fourier_re_neg]
    rw [he]
    exact hcert t

end AEGIS.KreinSlackV1

#print axioms AEGIS.KreinSlackV1.actual_margin_with_slack
#print axioms AEGIS.KreinSlackV1.zero_quadratic_margin_with_slack
#print axioms AEGIS.KreinSlackV1.zero_quadratic_margin_with_slack_from_genuine_certificate
#print axioms AEGIS.KreinSlackV1.fourier_finset_sum
#print axioms AEGIS.KreinSlackV1.zero_quadratic_margin_with_slack_of_hats
