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
import CvSRoughV1
import RHKreinZetaBridgeV3

/-!
# Krein certificate with slack for rough log profiles (CvS step 5.4b, ring tree)

`RHKreinZetaBridgeV4.certificate_slack` bounds the zero quadratic of a smooth moment-zero packet.
The Feshbach complement `w = G − P_V G` of the trigonometric low block is only integrable, so this
file restates the certificate for log profiles and extends it with `CvSRoughV1.rough_of_smooth`:

* `krein_smooth`: for smooth moment-zero `G` supported in `[lo, hi]`, `hi − lo < L`, the certificate
  `W(S − m) + Re Σ 𝓕Hᵢ + δ-columns ≥ 0` gives `m ∫ |𝓕G(t/2π)|² ≤ ∫ S |𝓕G(t/2π)|²`
  (the moment-zero factorization `G = χ'' − χ/4` and `RHKreinCertificateV1.certificate_lower_bound`);
* `krein_rough`: the same for integrable moment-zero `G` vanishing outside `[lo, hi]`;
* `krein_slack_rough`: with `S = ScertM M + s`, `s` bounded measurable,
  `m ∫ |𝓕w|² ≤ ∫ ScertM M |𝓕w|² + ∫ s |𝓕w|²` for the rough complement.

No window/prime condition is needed here: the zero-quadratic identity is not used. The support
length must be strictly below the Krein window `L` (mollification widens it), so in a Feshbach
certificate the trigonometric window must be strictly shorter than the Krein window. Not RH.
-/

open MeasureTheory FourierTransform Complex Set Filter
open scoped ContDiff SchwartzMap

noncomputable section

namespace AEGIS.CvSKreinRoughV1

open AEGIS.CvSRoughV1 AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

/-- Moment-zero profiles factor through `χ'' − χ/4`: `|𝓕G(t/2π)|² = W(t) |𝓕χ(t/2π)|²`. -/
theorem energy_factor {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) {lo hi : ℝ} (hlh : lo ≤ hi)
    (hts : tsupport G ⊆ Icc lo hi) (hmom : MomentZero G) :
    ∃ chi : ℝ → ℂ, ContDiff ℝ ∞ chi ∧ tsupport chi ⊆ Icc lo hi ∧
      ∀ t, energy G t = Wt t * Complex.normSq (𝓕 chi (t / (2 * Real.pi))) := by
  obtain ⟨chi, hc, hs, hode⟩ :=
    AEGIS.RHKreinFactorV13.moment_zero_parametrization G lo hi hlh hG hts hmom.1 hmom.2
  refine ⟨chi, hc, hs, fun t => ?_⟩
  have hts' : tsupport chi ⊆ Set.Ioo (lo - 1) (hi + 1) :=
    hs.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hint := AEGIS.RHKreinDeltaPairingV1.iteratedDeriv_integrable chi hc _ _ hts'
  have hall : ∀ n : ℕ, (n : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (iteratedDeriv n chi) :=
    fun n _ => hint n
  have h2 : iteratedDeriv 2 chi = deriv (deriv chi) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hGe : G = fun u => iteratedDeriv 2 chi u - (1 / 4 : ℂ) * chi u := by
    funext u; rw [hode u, h2]
  have hF := Real.fourier_iteratedDeriv (N := ⊤) (n := 2) hc hall le_top
  have h0 : Integrable chi := by simpa using hint 0
  rw [energy, hGe, fourier_lin _ _ (hint 2) h0, hF]
  set ξ := t / (2 * Real.pi)
  have hξ : 2 * Real.pi * ξ = t := by
    simp only [ξ]; field_simp
  have hfac : (2 * (Real.pi : ℂ) * I * (ξ : ℂ)) ^ 2 • 𝓕 chi ξ - (1 / 4 : ℂ) * 𝓕 chi ξ =
      ((-(t ^ 2 + 1 / 4) : ℝ) : ℂ) * 𝓕 chi ξ := by
    rw [smul_eq_mul, ← hξ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hfac, Complex.normSq_mul, Complex.normSq_ofReal, Wt]
  ring

theorem fourier_normSq_integrable {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hcs : HasCompactSupport G) :
    Integrable fun ν => Complex.normSq (𝓕 G ν) := by
  set ψ : 𝓢(ℝ, ℂ) := hcs.toSchwartzMap hG
  have hi : Integrable (𝓕 G) := by
    have h := (𝓕 ψ).integrable (μ := volume)
    rw [SchwartzMap.fourier_coe] at h
    exact h
  have hc : Continuous (𝓕 G) := by
    have h := (𝓕 ψ).continuous
    rw [SchwartzMap.fourier_coe] at h
    exact h
  refine (hi.norm.bdd_mul (c := ∫ x, ‖G x‖) hc.norm.aestronglyMeasurable
    (Eventually.of_forall fun ν => ?_)).congr (Eventually.of_forall fun ν => ?_)
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact AEGIS.RHKreinDeltaPairingV1.norm_fourier_le G ν
  · simp only [Complex.normSq_eq_norm_sq]; ring

/-- **Krein certificate for smooth log profiles.** -/
theorem krein_smooth (S : ℝ → ℝ) (L m : ℝ)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (S t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re)
    {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) {lo hi : ℝ} (hlh : lo ≤ hi) (hts : tsupport G ⊆ Icc lo hi)
    (hlen : hi - lo < L) (hmom : MomentZero G) (hSE : Integrable fun t => S t * energy G t) :
    m * ∫ t, energy G t ≤ ∫ t, S t * energy G t := by
  obtain ⟨chi, hc, hs, hE⟩ := energy_factor hG hlh hts hmom
  set ε := (L - (hi - lo)) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hts' : tsupport chi ⊆ Set.Ioo (lo - ε) (hi + ε) :=
    hs.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hba : (hi + ε) - (lo - ε) = L := by rw [hε]; ring
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hEν : ∀ ν : ℝ, Wt (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν) =
      energy G (2 * Real.pi * ν) := by
    intro ν; rw [hE, two_pi_div]
  have hcs : HasCompactSupport G :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport _).trans hts)
  have hW : Integrable (fun ν => Wt (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν)) := by
    refine (fourier_normSq_integrable hG hcs).congr (Eventually.of_forall fun ν => ?_)
    show _ = Wt (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν)
    rw [hEν, energy, two_pi_div]
  have hWS : Integrable (fun ν => Wt (2 * Real.pi * ν) * S (2 * Real.pi * ν) *
      Complex.normSq (𝓕 chi ν)) := by
    refine (hSE.comp_mul_left' h2pi).congr (Eventually.of_forall fun ν => ?_)
    show S (2 * Real.pi * ν) * energy G (2 * Real.pi * ν) = _
    rw [← hEν]; ring
  have hcert' : ∀ ξ : ℝ, 0 ≤ Wt (2 * Real.pi * ξ) * (S (2 * Real.pi * ξ) - m) +
      (∑ i, 𝓕 (H i) ξ).re + ∑ l, 2 * (d l * ((2 * Real.pi * I * ξ) ^ j l *
        Complex.exp (↑(2 * Real.pi * ξ * L) * I))).re := by
    intro ξ
    have h := hcert (2 * Real.pi * ξ)
    rw [two_pi_div] at h
    have e1 : ∀ l, (I * (((2 * Real.pi * ξ : ℝ)) : ℂ)) ^ j l = (2 * (Real.pi : ℂ) * I * ξ) ^ j l := by
      intro l; push_cast; ring_nf
    simp only [e1] at h
    exact h
  have hHs' : ∀ i u, |u| < (hi + ε) - (lo - ε) → H i u = 0 := by
    rw [hba]; exact hHs
  have key := AEGIS.RHKreinCertificateV1.certificate_lower_bound chi hc _ _ hts' L hba.le
    (fun ν => Wt (2 * Real.pi * ν)) (fun ν => S (2 * Real.pi * ν)) m H hHc hHi hFH hHs' d j
    hWS hW hcert'
  have e2 : (∫ ν, Wt (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν)) =
      (1 / (2 * Real.pi)) * ∫ t, energy G t := by
    rw [← integral_two_pi (energy G)]; congr 1; funext ν; exact hEν ν
  have e3 : (∫ ν, Wt (2 * Real.pi * ν) * S (2 * Real.pi * ν) * Complex.normSq (𝓕 chi ν)) =
      (1 / (2 * Real.pi)) * ∫ t, S t * energy G t := by
    rw [← integral_two_pi (fun t => S t * energy G t)]; congr 1; funext ν
    show _ = S (2 * Real.pi * ν) * energy G (2 * Real.pi * ν)
    rw [← hEν]; ring
  rw [e2, e3, mul_left_comm] at key
  exact le_of_mul_le_mul_left key (by positivity)

/-- **Krein certificate for rough log profiles.** -/
theorem krein_rough (S : ℝ → ℝ) (L m : ℝ)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (S t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re)
    {G : ℝ → ℂ} (hG : Integrable G) {lo hi : ℝ} (hlh : lo ≤ hi)
    (hsupp : Function.support G ⊆ Icc lo hi) (hlen : hi - lo < L) (hmom : MomentZero G)
    (hE : Integrable (energy G)) (hSE : Integrable fun t => S t * energy G t) :
    m * ∫ t, energy G t ≤ ∫ t, S t * energy G t :=
  rough_of_smooth S m L
    (fun _ hF _ _ hlh' hts' hlen' hmom' hSF =>
      krein_smooth S L m H hHc hHi hFH hHs d j hcert hF hlh' hts' hlen' hmom' hSF)
    hG hlh hsupp hlen hmom hE hSE

/-- **Krein certificate with slack for the rough Feshbach complement.** -/
theorem krein_slack_rough (M : ℕ) (L m : ℝ) (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ)
    (hsB : ∀ t, |s t| ≤ B)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {w : ℝ → ℂ} (hw : Integrable w) {lo hi : ℝ} (hlh : lo ≤ hi)
    (hsupp : Function.support w ⊆ Icc lo hi) (hlen : hi - lo < L) (hmom : MomentZero w)
    (hE : Integrable (energy w)) (hSE : Integrable fun t => ScertM M t * energy w t) :
    m * ∫ t, energy w t ≤ (∫ t, ScertM M t * energy w t) + ∫ t, s t * energy w t := by
  have hsE : Integrable fun t => s t * energy w t :=
    hE.bdd_mul (c := B) hsm.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hsB t)
  have hSE' : Integrable fun t => (ScertM M t + s t) * energy w t :=
    (hSE.add hsE).congr (Eventually.of_forall fun t => by simp only [Pi.add_apply]; ring)
  have h := krein_rough (fun t => ScertM M t + s t) L m H hHc hHi hFH hHs d j
    (fun t => by have := hcert t; linarith) hw hlh hsupp hlen hmom hE hSE'
  rw [← integral_add hSE hsE]
  refine h.trans (le_of_eq ?_)
  congr 1; funext t; ring

end AEGIS.CvSKreinRoughV1

#print axioms AEGIS.CvSKreinRoughV1.energy_factor
#print axioms AEGIS.CvSKreinRoughV1.krein_smooth
#print axioms AEGIS.CvSKreinRoughV1.krein_rough
#print axioms AEGIS.CvSKreinRoughV1.krein_slack_rough
