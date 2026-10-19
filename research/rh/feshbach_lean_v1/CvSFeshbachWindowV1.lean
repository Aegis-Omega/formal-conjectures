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
import CvSTraceV1
import CvSRingBridgeV1

/-!
# The Feshbach window theorem, with its numerical inputs as hypotheses (CvS step 6, ring tree)

For a moment-zero packet `g` of log-width `2r < log (M+1)`, `RHKreinZetaBridgeV3` gives
`Re Σ_ρ Z_ρ = (1/2π) Q(G)` with `G = Gm g` and `Q(F) = ∫ ScertM M (t) |𝓕F(t/2π)|² dt`.
Splitting `G = v + w`,

  `Q(v + w) = Q(v) + 2 X(v, w) + Q(w)`,   `X(v, w) = ∫ ScertM M (t) Re(𝓕v · conj 𝓕w)(t/2π) dt`

(`quad_add`), and the Schur step (`feshbach_combine`): if `c E(w) ≤ Q(w)`, `X² ≤ K E(w)` and
`K/c ≤ Q(v)` then `Q(v + w) ≥ 0`. `window_nonneg` states this for packets;
`window_nonneg_of_krein` replaces `c E(w) ≤ Q(w)` by the Krein certificate with slack and the trace
integral (`CvSTraceV1.complement_bound`).

What is *not* proved here, and remains as hypotheses: the pointwise Krein certificate inequality,
the trace integral `∫ s R ≤ T`, the cross bound `X² ≤ K E(w)` and the low-block bound
`K/c ≤ Q(v)`. These are the interval-arithmetic parts of the Arb certificates. Not RH.
-/

open MeasureTheory FourierTransform Complex Set Filter
open scoped ComplexConjugate

noncomputable section

namespace AEGIS.CvSFeshbachWindowV1

open AEGIS.CvSRoughV1 AEGIS.CvSPlancherelRoughV1 AEGIS.CvSTraceV1 AEGIS.CvSDigammaSeriesV1
open AEGIS.CvSArchSourceV1 AEGIS.CvSQuadV1 AEGIS.CvSRingBridgeV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

/-- The cross density `Re(𝓕v(t/2π) · conj 𝓕w(t/2π))`. -/
def cross (v w : ℝ → ℂ) (t : ℝ) : ℝ :=
  (𝓕 v (t / (2 * Real.pi)) * conj (𝓕 w (t / (2 * Real.pi)))).re

theorem fourier_add' {v w : ℝ → ℂ} (hv : Integrable v) (hw : Integrable w) (ξ : ℝ) :
    𝓕 (fun u => v u + w u) ξ = 𝓕 v ξ + 𝓕 w ξ := by
  have h := fourier_lin v w hv hw (-1) ξ
  have e : (fun u => v u - (-1 : ℂ) * w u) = fun u => v u + w u := by funext u; ring
  rw [e] at h
  rw [h]; ring

theorem energy_add {v w : ℝ → ℂ} (hv : Integrable v) (hw : Integrable w) (t : ℝ) :
    energy (fun u => v u + w u) t = energy v t + 2 * cross v w t + energy w t := by
  simp only [energy, cross]
  rw [fourier_add' hv hw, Complex.normSq_add]
  ring

theorem abs_cross_le (v w : ℝ → ℂ) (t : ℝ) : |cross v w t| ≤ (energy v t + energy w t) / 2 := by
  simp only [cross, energy]
  set a := 𝓕 v (t / (2 * Real.pi))
  set b := 𝓕 w (t / (2 * Real.pi))
  have h1 : |(a * conj b).re| ≤ ‖a‖ * ‖b‖ := by
    calc |(a * conj b).re| ≤ ‖a * conj b‖ := Complex.abs_re_le_norm _
      _ = ‖a‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem cross_continuous {v w : ℝ → ℂ} (hv : Integrable v) (hw : Integrable w) :
    Continuous (cross v w) := by
  have hv' := (fourier_continuous hv).comp (continuous_id.div_const (2 * Real.pi))
  have hw' := (fourier_continuous hw).comp (continuous_id.div_const (2 * Real.pi))
  exact Complex.continuous_re.comp (hv'.mul (Complex.continuous_conj.comp hw'))

/-- **Sesquilinear expansion of the critical-line form.** -/
theorem quad_add (S : ℝ → ℝ) (hSm : AEStronglyMeasurable S) {v w : ℝ → ℂ} (hv : Integrable v)
    (hw : Integrable w) (hSv : Integrable fun t => S t * energy v t)
    (hSw : Integrable fun t => S t * energy w t) :
    ∫ t, S t * energy (fun u => v u + w u) t =
      (∫ t, S t * energy v t) + 2 * (∫ t, S t * cross v w t) + ∫ t, S t * energy w t := by
  have hX : Integrable fun t => S t * cross v w t := by
    refine ((hSv.norm.add hSw.norm).div_const 2).mono'
      (hSm.mul (cross_continuous hv hw).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    have h0v : 0 ≤ energy v t := Complex.normSq_nonneg _
    have h0w : 0 ≤ energy w t := Complex.normSq_nonneg _
    show ‖S t * cross v w t‖ ≤ (‖S t * energy v t‖ + ‖S t * energy w t‖) / 2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg h0v, abs_of_nonneg h0w]
    have := mul_le_mul_of_nonneg_left (abs_cross_le v w t) (abs_nonneg (S t))
    linarith
  have hpt : ∀ t, S t * energy (fun u => v u + w u) t =
      S t * energy v t + 2 * (S t * cross v w t) + S t * energy w t := fun t => by
    rw [energy_add hv hw]; ring
  simp_rw [hpt]
  have h1 : ∫ t, (S t * energy v t + 2 * (S t * cross v w t)) + S t * energy w t =
      (∫ t, S t * energy v t + 2 * (S t * cross v w t)) + ∫ t, S t * energy w t :=
    integral_add (hSv.add (hX.const_mul 2)) hSw
  have h2 : ∫ t, S t * energy v t + 2 * (S t * cross v w t) =
      (∫ t, S t * energy v t) + ∫ t, 2 * (S t * cross v w t) :=
    integral_add hSv (hX.const_mul 2)
  rw [h1, h2, integral_const_mul]

theorem archTerm_continuous (k : ℕ) : Continuous (archTerm k) := by
  have h : ∀ r : ℝ, archWidth k ^ 2 + r ^ 2 ≠ 0 := fun r => by
    have := archWidth_pos k; positivity
  unfold archTerm
  exact continuous_const.sub (continuous_const.div (by fun_prop) h)

theorem hplus_measurable : Measurable hplus := by
  have h : Measurable fun r => ∑' k, archTerm k r := by
    refine measurable_of_tendsto_metrizable
      (f := fun N r => ∑ k ∈ Finset.range N, archTerm k r)
      (fun N => (continuous_finsetSum _ fun k _ => archTerm_continuous k).measurable) ?_
    exact tendsto_pi_nhds.2 fun r => (archTerm_summable r).hasSum.tendsto_sum_nat
  have e : hplus = fun r => (∑' k, archTerm k r) -
      (Real.eulerMascheroniConstant + Real.log Real.pi) := funext hplus_eq_tsum
  rw [e]
  exact h.sub_const _

theorem scertM_measurable (M : ℕ) : Measurable (ScertM M) := by
  rw [scertM_eq_qsym]
  unfold qsym
  refine hplus_measurable.sub (Finset.measurable_sum _ fun j _ => ?_)
  exact measurable_const.mul (by fun_prop)

/-- **The Schur step.** -/
theorem feshbach_combine {Qv Qw X Ew K c : ℝ} (hc : 0 < c) (hEw : 0 ≤ Ew) (hK : 0 ≤ K)
    (hw : c * Ew ≤ Qw) (hX : X ^ 2 ≤ K * Ew) (hv : K / c ≤ Qv) : 0 ≤ Qv + 2 * X + Qw := by
  set a := K / c with ha'
  set b := c * Ew with hb'
  have ha : 0 ≤ a := div_nonneg hK hc.le
  have hb : 0 ≤ b := mul_nonneg hc.le hEw
  have hab : K * Ew = a * b := by
    rw [ha', hb']; field_simp
  rw [hab] at hX
  have key : -(2 * X) ≤ a + b := by
    by_contra hneg
    have h := mul_self_lt_mul_self (add_nonneg ha hb) (not_le.mp hneg)
    nlinarith [sq_nonneg (a - b)]
  linarith

theorem gm_momentZero (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    MomentZero (Gm g) :=
  ⟨Gm_moment_minus g hm, Gm_moment_plus g hm⟩

/-- `Re Σ_ρ Z_ρ = (1/2π) ∫ ScertM M (t) |𝓕(Gm g)(t/2π)|² dt`. -/
theorem zero_quadratic_eq_energy (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (r a : ℝ) (hw : HalfWidthAt g r a) (M : ℕ) (hM : 2 * r < Real.log ((M + 1 : ℕ) : ℝ)) :
    (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re =
      (1 / (2 * Real.pi)) * ∫ t, ScertM M t * energy (Gm g) t := by
  rw [zero_quadratic_eq_scertM g hm r a hw M hM]
  congr 2
  funext t
  rw [Nr_eq]
  rfl

/-- **The Feshbach window theorem**, with the complement, cross and low-block bounds as
hypotheses. -/
theorem window_nonneg (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (M : ℕ) (hM : 2 * r < Real.log ((M + 1 : ℕ) : ℝ))
    (v w : ℝ → ℂ) (hdec : Gm g = fun u => v u + w u) (hv : Integrable v) (hwi : Integrable w)
    (hSv : Integrable fun t => ScertM M t * energy v t)
    (hSw : Integrable fun t => ScertM M t * energy w t)
    {K c : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hcomp : c * ∫ t, energy w t ≤ ∫ t, ScertM M t * energy w t)
    (hcross : (∫ t, ScertM M t * cross v w t) ^ 2 ≤ K * ∫ t, energy w t)
    (hlow : K / c ≤ ∫ t, ScertM M t * energy v t) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  rw [zero_quadratic_eq_energy g hm r a hw M hM, hdec,
    quad_add (ScertM M) (scertM_measurable M).aestronglyMeasurable hv hwi hSv hSw]
  have h := feshbach_combine hc (integral_nonneg fun t => Complex.normSq_nonneg _) hK hcomp
    hcross hlow
  exact mul_nonneg (by positivity) h

/-- **The Feshbach window theorem from a Krein certificate with slack.** The complement bound is
`CvSTraceV1.complement_bound` with `c = m − T/2π`; the cross and low-block bounds remain
hypotheses. -/
theorem window_nonneg_of_krein (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
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
    (cf : ℝ → Fin p → ℂ) (hR : Integrable fun t => s t * trialDist lo hi U cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist lo hi U cf t ≤ T) (hcpos : 0 < m - T / (2 * Real.pi))
    {K : ℝ} (hK : 0 ≤ K)
    (hcross : (∫ t, ScertM M t * cross v w t) ^ 2 ≤ K * ∫ t, energy w t)
    (hlow : K / (m - T / (2 * Real.pi)) ≤ ∫ t, ScertM M t * energy v t) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  window_nonneg g hm r a hw M hM v w hdec hv hwi hSv hSw hcpos hK
    (complement_bound M L m s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert hwi hC hlh hsupp hlen
      hmomw hEw hSw U hU horth cf hR hT)
    hcross hlow

end AEGIS.CvSFeshbachWindowV1

#print axioms AEGIS.CvSFeshbachWindowV1.energy_add
#print axioms AEGIS.CvSFeshbachWindowV1.quad_add
#print axioms AEGIS.CvSFeshbachWindowV1.scertM_measurable
#print axioms AEGIS.CvSFeshbachWindowV1.feshbach_combine
#print axioms AEGIS.CvSFeshbachWindowV1.zero_quadratic_eq_energy
#print axioms AEGIS.CvSFeshbachWindowV1.window_nonneg
#print axioms AEGIS.CvSFeshbachWindowV1.window_nonneg_of_krein
