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
import CvSPlancherelRoughV1
import CvSKreinRoughV1

/-!
# The trace bound and the Feshbach complement inequality (CvS step 5.6a, ring tree)

For `w` vanishing outside `[lo, hi]` and orthogonal (in `L²[lo, hi]`) to continuous `U₁, …, U_p`,
`𝓕w(t/2π) = ∫_{lo}^{hi} w(x) conj(e^{ixt} − Σ cᵢ Uᵢ(x)) dx` for every choice of `c`, so by
Cauchy–Schwarz

  `|𝓕w(t/2π)|² ≤ ‖w‖² R(t)`,   `R(t) = ∫_{lo}^{hi} |e^{ixt} − Σ cᵢ(t) Uᵢ(x)|² dx`
  (`energy_le_dist`).

With `s ≥ 0` and `∫ s R ≤ T`, the slack of the Krein certificate is at most `T ‖w‖² = (T/2π) E(w)`
(`slack_le_trace`, using `CvSPlancherelRoughV1.energy_eq_two_pi_L2`), and `complement_bound`:

  `(m − T/2π) ∫ |𝓕w(t/2π)|² dt ≤ ∫ ScertM M (t) |𝓕w(t/2π)|² dt`

for every bounded integrable moment-zero `w` of support length `< L` orthogonal to the `Uᵢ`. This is
the complement block of the Feshbach certificates (`c_∞ = m − T/2π`), with the Krein inequality
and the trace integral `∫ s R` as hypotheses. Not RH.
-/

open MeasureTheory FourierTransform Complex Set Filter
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace AEGIS.CvSTraceV1

open AEGIS.CvSRoughV1 AEGIS.CvSPlancherelRoughV1 AEGIS.CvSKreinRoughV1
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

theorem L2_norm_sq {μ : Measure ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℂ) (hf.toLp f) (hf.toLp f)
  have h2 : (∫ a, ⟪(hf.toLp f : ℝ → ℂ) a, (hf.toLp f : ℝ → ℂ) a⟫_ℂ ∂μ) =
      ∫ a, (((‖f a‖ ^ 2 : ℝ)) : ℂ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with a ha
    rw [ha, inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h2, integral_complex_ofReal] at h
  have h3 := congrArg Complex.re h
  rw [Complex.ofReal_re] at h3
  rw [← h3]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

/-- **Cauchy–Schwarz** for `L²` functions. -/
theorem cauchy_schwarz {μ : Measure ℝ} {f g : ℝ → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * conj (g x) ∂μ‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂μ) * ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (hg.toLp g) (hf.toLp f)
  rw [L2.inner_def] at h
  have e : (∫ a, ⟪(hg.toLp g : ℝ → ℂ) a, (hf.toLp f : ℝ → ℂ) a⟫_ℂ ∂μ) =
      ∫ x, f x * conj (g x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, hf.coeFn_toLp] with a h1 h2
    rw [h1, h2]
    simp
  rw [e] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, L2_norm_sq hf, L2_norm_sq hg] at h2
  linarith

theorem memLp_of_continuous {lo hi : ℝ} {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Icc lo hi)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hC))

theorem memLp_of_bound {lo hi C : ℝ} {f : ℝ → ℂ} (hf : AEStronglyMeasurable f)
    (hC : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 (volume.restrict (Icc lo hi)) :=
  MemLp.of_bound hf.restrict C (Eventually.of_forall hC)

theorem integrableOn_mul_conj {w f : ℝ → ℂ} {lo hi C : ℝ} (hwm : AEStronglyMeasurable w)
    (hC : ∀ x, ‖w x‖ ≤ C) (hf : Continuous f) :
    IntegrableOn (fun x => w x * conj (f x)) (Icc lo hi) := by
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn hf.continuousOn
  have h := MemLp.of_bound (p := 1) (μ := volume.restrict (Icc lo hi))
    (hwm.restrict.mul (Complex.continuous_conj.comp hf).aestronglyMeasurable.restrict) (C * D)
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun x hx => by
      show ‖w x * conj (f x)‖ ≤ C * D
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hC x) (hD x hx) (norm_nonneg _) ((norm_nonneg _).trans (hC x))))
  exact memLp_one_iff_integrable.mp h

/-- `𝓕w(t/2π)` is the `L²[lo, hi]` pairing of `w` with `e^{ixt}`. -/
theorem fourier_eq_pairing {w : ℝ → ℂ} {lo hi : ℝ} (hsupp : Function.support w ⊆ Icc lo hi)
    (t : ℝ) :
    𝓕 w (t / (2 * Real.pi)) = ∫ x in Icc lo hi, w x * conj (Complex.exp (↑(x * t) * I)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · congr 1
    funext x
    rw [smul_eq_mul, mul_comm, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  · intro x hx
    have : w x = 0 := by
      by_contra h
      exact hx (hsupp h)
    rw [this, zero_mul]

/-- **Trace bound.** -/
theorem energy_le_dist {w : ℝ → ℂ} {lo hi C : ℝ} (hsupp : Function.support w ⊆ Icc lo hi)
    (hwm : AEStronglyMeasurable w) (hC : ∀ x, ‖w x‖ ≤ C)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, Continuous (U i))
    (horth : ∀ i, ∫ x in Icc lo hi, w x * conj (U i x) = 0) (c : Fin p → ℂ) (t : ℝ) :
    energy w t ≤ (∫ x in Icc lo hi, ‖w x‖ ^ 2) *
      ∫ x in Icc lo hi, ‖Complex.exp (↑(x * t) * I) - ∑ i, c i * U i x‖ ^ 2 := by
  set g : ℝ → ℂ := fun x => Complex.exp (↑(x * t) * I) - ∑ i, c i * U i x with hg
  have hw2 : MemLp w 2 (volume.restrict (Icc lo hi)) := memLp_of_bound hwm hC
  have hgc : Continuous g := by
    refine Continuous.sub (by fun_prop) (continuous_finsetSum _ fun i _ => ?_)
    exact continuous_const.mul (hU i)
  have hwU : ∀ i, IntegrableOn (fun x => w x * conj (U i x)) (Icc lo hi) := fun i =>
    integrableOn_mul_conj hwm hC (hU i)
  have hsplit : (∫ x in Icc lo hi, w x * conj (Complex.exp (↑(x * t) * I))) =
      ∫ x in Icc lo hi, w x * conj (g x) := by
    have hpt : ∀ x, w x * conj (Complex.exp (↑(x * t) * I)) =
        w x * conj (g x) + ∑ i, conj (c i) * (w x * conj (U i x)) := fun x => by
      simp only [hg, map_sub, map_sum, map_mul]
      have e : w x * ∑ i, conj (c i) * conj (U i x) = ∑ i, conj (c i) * (w x * conj (U i x)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [mul_sub, e]
      ring
    simp_rw [hpt]
    have hint : ∀ i ∈ (Finset.univ : Finset (Fin p)),
        IntegrableOn (fun x => conj (c i) * (w x * conj (U i x))) (Icc lo hi) := fun i _ =>
      (hwU i).const_mul _
    rw [integral_add, integral_finsetSum _ hint]
    · simp only [integral_const_mul, horth, mul_zero, Finset.sum_const_zero, add_zero]
    · exact integrableOn_mul_conj hwm hC hgc
    · exact integrable_finsetSum _ hint
  rw [energy, fourier_eq_pairing hsupp, hsplit, Complex.normSq_eq_norm_sq]
  exact cauchy_schwarz hw2 (memLp_of_continuous hgc)

/-- The trial distance `R(t) = ∫_{lo}^{hi} |e^{ixt} − Σ cᵢ(t) Uᵢ(x)|² dx`. -/
def trialDist {p : ℕ} (lo hi : ℝ) (U : Fin p → ℝ → ℂ) (c : ℝ → Fin p → ℂ) (t : ℝ) : ℝ :=
  ∫ x in Icc lo hi, ‖Complex.exp (↑(x * t) * I) - ∑ i, c t i * U i x‖ ^ 2

/-- **The slack is paid by the trace.** -/
theorem slack_le_trace {w : ℝ → ℂ} {lo hi C : ℝ} (hw : Integrable w)
    (hsupp : Function.support w ⊆ Icc lo hi) (hC : ∀ x, ‖w x‖ ≤ C)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, Continuous (U i))
    (horth : ∀ i, ∫ x in Icc lo hi, w x * conj (U i x) = 0)
    (s : ℝ → ℝ) (hs0 : ∀ t, 0 ≤ s t) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B)
    (c : ℝ → Fin p → ℂ) (hR : Integrable fun t => s t * trialDist lo hi U c t)
    {T : ℝ} (hT : ∫ t, s t * trialDist lo hi U c t ≤ T) (hE : Integrable (energy w)) :
    ∫ t, s t * energy w t ≤ T / (2 * Real.pi) * ∫ t, energy w t := by
  set N2 := ∫ x in Icc lo hi, ‖w x‖ ^ 2 with hN2
  have hN0 : 0 ≤ N2 := setIntegral_nonneg measurableSet_Icc fun x _ => by positivity
  have hsE : Integrable fun t => s t * energy w t :=
    hE.bdd_mul (c := B) hsm.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hsB t)
  have h1 : ∫ t, s t * energy w t ≤ N2 * ∫ t, s t * trialDist lo hi U c t := by
    rw [← integral_const_mul]
    refine integral_mono hsE (hR.const_mul N2) fun t => ?_
    have h := energy_le_dist hsupp hw.aestronglyMeasurable hC U hU horth (c t) t
    have := mul_le_mul_of_nonneg_left h (hs0 t)
    simp only [trialDist]
    linarith
  have hN2E : N2 = (1 / (2 * Real.pi)) * ∫ t, energy w t := by
    rw [energy_eq_two_pi_L2 hw hC hE, hN2, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · field_simp
      congr 1; funext x; rw [Complex.normSq_eq_norm_sq]
    · intro x hx
      have : w x = 0 := by
        by_contra h
        exact hx (hsupp h)
      rw [this, norm_zero]; ring
  calc ∫ t, s t * energy w t ≤ N2 * ∫ t, s t * trialDist lo hi U c t := h1
    _ ≤ N2 * T := mul_le_mul_of_nonneg_left hT hN0
    _ = T / (2 * Real.pi) * ∫ t, energy w t := by rw [hN2E]; ring

/-- **The Feshbach complement inequality** `c_∞ E(w) ≤ Q(w)`, `c_∞ = m − T/2π`. -/
theorem complement_bound (M : ℕ) (L m : ℝ) (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ)
    (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {w : ℝ → ℂ} (hw : Integrable w) {C : ℝ} (hC : ∀ x, ‖w x‖ ≤ C) {lo hi : ℝ} (hlh : lo ≤ hi)
    (hsupp : Function.support w ⊆ Icc lo hi) (hlen : hi - lo < L) (hmom : MomentZero w)
    (hE : Integrable (energy w)) (hSE : Integrable fun t => ScertM M t * energy w t)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, Continuous (U i))
    (horth : ∀ i, ∫ x in Icc lo hi, w x * conj (U i x) = 0)
    (c : ℝ → Fin p → ℂ) (hR : Integrable fun t => s t * trialDist lo hi U c t)
    {T : ℝ} (hT : ∫ t, s t * trialDist lo hi U c t ≤ T) :
    (m - T / (2 * Real.pi)) * ∫ t, energy w t ≤ ∫ t, ScertM M t * energy w t := by
  have h1 := krein_slack_rough M L m s hsm B hsB H hHc hHi hFH hHs d j hcert hw hlh hsupp hlen
    hmom hE hSE
  have h2 := slack_le_trace hw hsupp hC U hU horth s hs0 hsm B hsB c hR hT hE
  rw [sub_mul]
  linarith

end AEGIS.CvSTraceV1

#print axioms AEGIS.CvSTraceV1.cauchy_schwarz
#print axioms AEGIS.CvSTraceV1.fourier_eq_pairing
#print axioms AEGIS.CvSTraceV1.energy_le_dist
#print axioms AEGIS.CvSTraceV1.slack_le_trace
#print axioms AEGIS.CvSTraceV1.complement_bound
