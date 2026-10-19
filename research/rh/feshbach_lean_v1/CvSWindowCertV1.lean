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
import CvSFeshbachWindowV1

/-!
# A window certificate gives the arithmetic sign on the whole window (CvS step 6b, ring tree)

`CvSFeshbachWindowV1.window_nonneg_of_krein` takes the Feshbach split `Gm g = v + w` of one
packet as input. Here the split is constructed for every packet, so that the remaining
hypotheses no longer mention the packet:

* `exists_orth_coeffs`: for `G ∈ L²(μ)` and `U₁, …, U_p ∈ L²(μ)` there are coefficients `c` with
  `G − Σ cᵢ Uᵢ ⊥ Uⱼ` for all `j` (Mathlib's orthogonal projection onto the finite-dimensional span);
* `energy_translate`, `momentZero_translate`: the energy and the moment conditions are invariant
  under translation, so every packet is moved to `[0, 2r] ⊆ [0, L_T]`;
* `window_of_certificate`: if the low block `v_c = 1_{[0, L_T]} Σ cᵢ Uᵢ` (with moment-zero `Uᵢ`)
  satisfies the Krein, trace, cross and low-block bounds for every `c` and every admissible
  complement `w`, then `Re Σ_ρ Z_ρ(A_g) ≥ 0` for every moment-zero packet of log-width `2r ≤ L_T`.

The hypotheses of `window_of_certificate` are the certificate. They are not proved here. Not RH.
-/

open MeasureTheory FourierTransform Complex Set Filter
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace AEGIS.CvSWindowCertV1

open AEGIS.CvSRoughV1 AEGIS.CvSPlancherelRoughV1 AEGIS.CvSKreinRoughV1 AEGIS.CvSTraceV1
open AEGIS.CvSFeshbachWindowV1
open AEGIS.WeilCriticalLineKreinFormV1 AEGIS.RHDyadicDiagonalV13
open AEGIS.RHKreinZetaBridgeV1 AEGIS.RHKreinZetaBridgeV3

theorem inner_toLp {μ : Measure ℝ} {F H : ℝ → ℂ} (hF : MemLp F 2 μ) (hH : MemLp H 2 μ) :
    ⟪hF.toLp F, hH.toLp H⟫_ℂ = ∫ x, conj (F x) * H x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hH.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem integrable_conj_mul {μ : Measure ℝ} {F H : ℝ → ℂ} (hF : MemLp F 2 μ)
    (hH : MemLp H 2 μ) : Integrable (fun x => conj (F x) * H x) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hF.toLp F) (hH.toLp H)).congr ?_
  filter_upwards [hF.coeFn_toLp, hH.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- **Orthogonal projection onto a finite family.** -/
theorem exists_orth_coeffs {μ : Measure ℝ} {G : ℝ → ℂ} (hG : MemLp G 2 μ) {p : ℕ}
    {U : Fin p → ℝ → ℂ} (hU : ∀ i, MemLp (U i) 2 μ) :
    ∃ c : Fin p → ℂ, ∀ j, ∫ x, (G x - ∑ i, c i * U i x) * conj (U j x) ∂μ = 0 := by
  set u : Fin p → Lp ℂ 2 μ := fun i => (hU i).toLp (U i)
  set K := Submodule.span ℂ (Set.range u)
  have : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  have : CompleteSpace K := FiniteDimensional.complete ℂ K
  set g := hG.toLp G
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (K.starProjection_apply_mem g)
  refine ⟨c, fun j => ?_⟩
  have h0 := K.starProjection_inner_eq_zero g (u j) (Submodule.subset_span ⟨j, rfl⟩)
  rw [← hc, inner_sub_left, sum_inner] at h0
  simp only [inner_smul_left, u, g, inner_toLp] at h0
  -- h0 : ∫ conj G · Uⱼ − Σ conj cᵢ ∫ conj Uᵢ · Uⱼ = 0
  have hGj := integrable_conj_mul hG (hU j)
  have hij : ∀ i, Integrable (fun x => conj (U i x) * U j x) μ := fun i =>
    integrable_conj_mul (hU i) (hU j)
  have e1 : ∀ x, (G x - ∑ i, c i * U i x) * conj (U j x) =
      conj (conj (G x) * U j x - ∑ i, conj (c i) * (conj (U i x) * U j x)) := fun x => by
    simp only [map_sub, map_sum, map_mul, Complex.conj_conj]
    rw [sub_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e1]
  rw [integral_conj, integral_sub hGj (integrable_finsetSum _ fun i _ => (hij i).const_mul _),
    integral_finsetSum _ fun i _ => (hij i).const_mul _]
  simp only [integral_const_mul]
  rw [h0, map_zero]

theorem energy_translate (G : ℝ → ℂ) (a t : ℝ) : energy (fun u => G (u + a)) t = energy G t := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ ℝ) G a) (t / (2 * Real.pi))
  simp only [energy]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  change ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
    (G ∘ fun v => v + a) (t / (2 * Real.pi))‖ ^ 2 =
    ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) G (t / (2 * Real.pi))‖ ^ 2
  rw [h, Circle.norm_smul]

theorem momentZero_translate {G : ℝ → ℂ} (hG : MomentZero G) (a : ℝ) :
    MomentZero fun u => G (u + a) := by
  have key : ∀ c : ℝ, (∫ u, (Real.exp (c * u) : ℂ) * G (u + a)) =
      (Real.exp (-(c * a)) : ℂ) * ∫ x, (Real.exp (c * x) : ℂ) * G x := fun c => by
    rw [← integral_const_mul]
    have h := integral_add_right_eq_self (μ := volume) (fun x => (Real.exp (-(c * a)) : ℂ) *
      ((Real.exp (c * x) : ℂ) * G x)) a
    rw [← h]
    congr 1
    funext u
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  have e1 : ∀ F : ℝ → ℂ, (∫ u, (Real.exp (-u / 2) : ℂ) * F u) =
      ∫ u, (Real.exp ((-1 / 2) * u) : ℂ) * F u := fun F => by
    congr 1; funext u; rw [show -u / 2 = (-1 / 2) * u by ring]
  have e2 : ∀ F : ℝ → ℂ, (∫ u, (Real.exp (u / 2) : ℂ) * F u) =
      ∫ u, (Real.exp ((1 / 2) * u) : ℂ) * F u := fun F => by
    congr 1; funext u; rw [show u / 2 = (1 / 2) * u by ring]
  refine ⟨?_, ?_⟩
  · rw [e1, key, ← e1, hG.1, mul_zero]
  · rw [e2, key, ← e2, hG.2, mul_zero]

/-- The low block `v_c = 1_{[0, L_T]} Σ cᵢ Uᵢ`. -/
def lowBlock {p : ℕ} (LT : ℝ) (U : Fin p → ℝ → ℂ) (c : Fin p → ℂ) : ℝ → ℂ :=
  Set.indicator (Icc 0 LT) fun x => ∑ i, c i * U i x

/-- The complements `w = G − v_c` that occur: bounded, integrable, supported in `[0, L_T]`,
moment-zero, orthogonal to the `Uᵢ`, with integrable energy. -/
def Admissible {p : ℕ} (LT : ℝ) (U : Fin p → ℝ → ℂ) (w : ℝ → ℂ) : Prop :=
  Integrable w ∧ (∃ C, ∀ x, ‖w x‖ ≤ C) ∧ Function.support w ⊆ Icc 0 LT ∧ MomentZero w ∧
    (∀ i, ∫ x in Icc 0 LT, w x * conj (U i x) = 0) ∧ Integrable (energy w)

theorem integrable_weight_indicator {LT : ℝ} {f E : ℝ → ℂ} (hf : Continuous f)
    (hE : Continuous E) : Integrable fun u => E u * Set.indicator (Icc 0 LT) f u := by
  have e : (fun u => E u * Set.indicator (Icc 0 LT) f u) =
      Set.indicator (Icc 0 LT) (fun u => E u * f u) := by
    funext u
    by_cases hu : u ∈ Icc 0 LT <;> simp [hu]
  rw [e]
  exact (hE.mul hf).integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem lowBlock_continuous_sum {p : ℕ} {U : Fin p → ℝ → ℂ} (hU : ∀ i, Continuous (U i))
    (c : Fin p → ℂ) : Continuous fun x => ∑ i, c i * U i x :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (hU i)

theorem lowBlock_integrable {p : ℕ} {LT : ℝ} {U : Fin p → ℝ → ℂ} (hU : ∀ i, Continuous (U i))
    (c : Fin p → ℂ) : Integrable (lowBlock LT U c) :=
  (lowBlock_continuous_sum hU c).integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem lowBlock_bound {p : ℕ} {LT : ℝ} {U : Fin p → ℝ → ℂ} (hU : ∀ i, Continuous (U i))
    (c : Fin p → ℂ) : ∃ D, ∀ x, ‖lowBlock LT U c x‖ ≤ D := by
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := LT)).exists_bound_of_continuousOn
    (lowBlock_continuous_sum hU c).continuousOn
  refine ⟨max D 0, fun x => ?_⟩
  by_cases hx : x ∈ Icc 0 LT
  · simp only [lowBlock, Set.indicator_of_mem hx]
    exact (hD x hx).trans (le_max_left _ _)
  · simp only [lowBlock, Set.indicator_of_notMem hx, norm_zero]
    exact le_max_right _ _

theorem weighted_lowBlock {p : ℕ} {LT : ℝ} {U : Fin p → ℝ → ℂ} (hU : ∀ i, Continuous (U i))
    (c : Fin p → ℂ) {E : ℝ → ℂ} (hE : Continuous E) :
    ∫ u, E u * lowBlock LT U c u = ∑ i, c i * ∫ u, E u * Set.indicator (Icc 0 LT) (U i) u := by
  have hpt : ∀ u, E u * lowBlock LT U c u =
      ∑ i, c i * (E u * Set.indicator (Icc 0 LT) (U i) u) := fun u => by
    by_cases hu : u ∈ Icc 0 LT
    · simp only [lowBlock, Set.indicator_of_mem hu, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · simp [lowBlock, Set.indicator_of_notMem hu]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => (integrable_weight_indicator (hU i) hE).const_mul _]
  simp only [integral_const_mul]

theorem lowBlock_momentZero {p : ℕ} {LT : ℝ} {U : Fin p → ℝ → ℂ} (hU : ∀ i, Continuous (U i))
    (hUmom : ∀ i, MomentZero (Set.indicator (Icc 0 LT) (U i))) (c : Fin p → ℂ) :
    MomentZero (lowBlock LT U c) := by
  refine ⟨?_, ?_⟩
  · rw [weighted_lowBlock hU c (E := fun u => (Real.exp (-u / 2) : ℂ)) (by fun_prop)]
    exact Finset.sum_eq_zero fun i _ => by simp only [(hUmom i).1, mul_zero]
  · rw [weighted_lowBlock hU c (E := fun u => (Real.exp (u / 2) : ℂ)) (by fun_prop)]
    exact Finset.sum_eq_zero fun i _ => by simp only [(hUmom i).2, mul_zero]

theorem energy_continuous {w : ℝ → ℂ} (hw : Integrable w) : Continuous (energy w) :=
  Complex.continuous_normSq.comp
    ((fourier_continuous hw).comp (continuous_id.div_const (2 * Real.pi)))

theorem energy_sub_le {G v : ℝ → ℂ} (hG : Integrable G) (hv : Integrable v) (t : ℝ) :
    energy (fun x => G x - v x) t ≤ 2 * energy G t + 2 * energy v t := by
  have h := fourier_lin G v hG hv 1 (t / (2 * Real.pi))
  have e : (fun u => G u - (1 : ℂ) * v u) = fun u => G u - v u := by funext u; ring
  rw [e, one_mul] at h
  simp only [energy]
  rw [h, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h1 := norm_sub_le (𝓕 G (t / (2 * Real.pi))) (𝓕 v (t / (2 * Real.pi)))
  have h2 := norm_nonneg (𝓕 G (t / (2 * Real.pi)) - 𝓕 v (t / (2 * Real.pi)))
  nlinarith [sq_nonneg (‖𝓕 G (t / (2 * Real.pi))‖ - ‖𝓕 v (t / (2 * Real.pi))‖),
    norm_nonneg (𝓕 G (t / (2 * Real.pi))), norm_nonneg (𝓕 v (t / (2 * Real.pi)))]

/-- **A window certificate gives the sign on the whole window.** If the low block `v_c`
(moment-zero `Uᵢ` on `[0, L_T]`) and every admissible complement satisfy the Krein, trace,
cross and low-block bounds, then every moment-zero packet of log-width `2r ≤ L_T` has
`Re Σ_ρ Z_ρ(A_g) ≥ 0`. -/
theorem window_of_certificate (M : ℕ) (L LT m : ℝ) (hLT0 : 0 ≤ LT) (hLTL : LT < L)
    (hLTM : LT < Real.log ((M + 1 : ℕ) : ℝ))
    (s : ℝ → ℝ) (hsm : Measurable s) (B : ℝ) (hsB : ∀ t, |s t| ≤ B) (hs0 : ∀ t, 0 ≤ s t)
    {n : ℕ} (H : Fin n → ℝ → ℂ) (hHc : ∀ i, Continuous (H i)) (hHi : ∀ i, Integrable (H i))
    (hFH : ∀ i, Integrable (𝓕 (H i))) (hHs : ∀ i u, |u| < L → H i u = 0)
    {k : ℕ} (d : Fin k → ℂ) (j : Fin k → ℕ)
    (hcert : ∀ t : ℝ, 0 ≤ Wt t * (ScertM M t - m) + (∑ i, 𝓕 (H i) (t / (2 * Real.pi))).re +
      ∑ l, 2 * (d l * ((I * (t : ℂ)) ^ j l * Complex.exp (↑(t * L) * I))).re + Wt t * s t)
    {p : ℕ} (U : Fin p → ℝ → ℂ) (hU : ∀ i, Continuous (U i))
    (hUmom : ∀ i, MomentZero (Set.indicator (Icc 0 LT) (U i)))
    (cf : ℝ → Fin p → ℂ) (hR : Integrable fun t => s t * trialDist 0 LT U cf t)
    {T : ℝ} (hT : ∫ t, s t * trialDist 0 LT U cf t ≤ T) (hcpos : 0 < m - T / (2 * Real.pi))
    (hEU : ∀ c, Integrable (energy (lowBlock LT U c)))
    (hSU : ∀ c, Integrable fun t => ScertM M t * energy (lowBlock LT U c) t)
    (K : (Fin p → ℂ) → ℝ) (hK : ∀ c, 0 ≤ K c)
    (hcross : ∀ c w, Admissible LT U w →
      (∫ t, ScertM M t * cross (lowBlock LT U c) w t) ^ 2 ≤ K c * ∫ t, energy w t)
    (hlow : ∀ c, K c / (m - T / (2 * Real.pi)) ≤ ∫ t, ScertM M t * energy (lowBlock LT U c) t)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) (r a : ℝ)
    (hw : HalfWidthAt g r a) (h2r : 2 * r ≤ LT) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  -- move the packet to `[0, 2r]`
  set lo := -a - r with hlo
  set G0 : ℝ → ℂ := fun u => Gm g (u + lo) with hG0def
  have hG0cd : ContDiff ℝ ∞ G0 := (Gm_contDiff g).comp (contDiff_id.add contDiff_const)
  have hG0c : Continuous G0 := hG0cd.continuous
  have hts := Gm_tsupport g r a hw
  have hG0s : Function.support G0 ⊆ Icc 0 LT := fun u hu => by
    have h1 : u + lo ∈ Icc (-a - r) (-a + r) := hts (subset_tsupport _ hu)
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hG0cs : HasCompactSupport G0 :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hG0s
  have hG0i : Integrable G0 := hG0c.integrable_of_hasCompactSupport hG0cs
  obtain ⟨CG, hCG⟩ := hG0c.bounded_above_of_compact_support hG0cs
  have hG0mom : MomentZero G0 := momentZero_translate (gm_momentZero g hm) lo
  have hEG : ∀ t, energy G0 t = energy (Gm g) t := fun t => energy_translate (Gm g) lo t
  have hEG0 : Integrable (energy G0) :=
    (fourier_normSq_integrable hG0cd hG0cs).comp_div (by positivity : (2 * Real.pi) ≠ 0)
  have hSG0 : Integrable fun t => ScertM M t * energy G0 t := by
    refine (scertMNr_integrable M g).congr (Eventually.of_forall fun t => ?_)
    show ScertM M t * Nr g t = ScertM M t * energy G0 t
    rw [hEG, Nr_eq]
    rfl
  -- the projection onto the low block
  obtain ⟨c, hc⟩ := exists_orth_coeffs (μ := volume.restrict (Icc 0 LT))
    (memLp_of_bound hG0c.aestronglyMeasurable hCG) (fun i => memLp_of_continuous (hU i))
  set v := lowBlock LT U c with hv
  set w : ℝ → ℂ := fun x => G0 x - v x with hwdef
  have hvi : Integrable v := lowBlock_integrable hU c
  obtain ⟨D, hD⟩ := lowBlock_bound (LT := LT) hU c
  have hwi : Integrable w := hG0i.sub hvi
  have hCw : ∀ x, ‖w x‖ ≤ CG + D := fun x =>
    (norm_sub_le _ _).trans (add_le_add (hCG x) (hD x))
  have hwsupp : Function.support w ⊆ Icc 0 LT := fun x hx => by
    by_contra hxn
    have h1 : G0 x = 0 := by
      by_contra h; exact hxn (hG0s h)
    have h2 : v x = 0 := by
      simp only [hv, lowBlock, Set.indicator_of_notMem hxn]
    exact hx (by simp only [hwdef, h1, h2, sub_zero])
  have hwmom : MomentZero w := by
    have hvmom := lowBlock_momentZero hU hUmom c
    have hwt : ∀ E : ℝ → ℂ, Continuous E →
        (∫ u, E u * w u) = (∫ u, E u * G0 u) - ∫ u, E u * v u := fun E hE => by
      have h1 : Integrable fun u => E u * G0 u :=
        (hE.mul hG0c).integrable_of_hasCompactSupport hG0cs.mul_left
      have h2 : Integrable fun u => E u * v u :=
        integrable_weight_indicator (lowBlock_continuous_sum hU c) hE
      rw [← integral_sub h1 h2]
      congr 1; funext u; simp only [hwdef]; ring
    refine ⟨?_, ?_⟩
    · rw [hwt (fun u => (Real.exp (-u / 2) : ℂ)) (by fun_prop), hG0mom.1, hvmom.1, sub_zero]
    · rw [hwt (fun u => (Real.exp (u / 2) : ℂ)) (by fun_prop), hG0mom.2, hvmom.2, sub_zero]
  have hworth : ∀ i, ∫ x in Icc 0 LT, w x * conj (U i x) = 0 := fun i => by
    rw [← hc i]
    refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    simp only [hwdef, hv, lowBlock, Set.indicator_of_mem hx]
  have hEw : Integrable (energy w) := by
    refine (((hEG0.const_mul 2).add ((hEU c).const_mul 2))).mono'
      (energy_continuous hwi).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    show ‖energy w t‖ ≤ 2 * energy G0 t + 2 * energy v t
    rw [Real.norm_of_nonneg (show 0 ≤ energy w t from Complex.normSq_nonneg _)]
    exact energy_sub_le hG0i hvi t
  have hSw : Integrable fun t => ScertM M t * energy w t := by
    refine ((hSG0.norm.const_mul 2).add ((hSU c).norm.const_mul 2)).mono'
      ((scertM_measurable M).aestronglyMeasurable.mul (energy_continuous hwi).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    have h0G : 0 ≤ energy G0 t := Complex.normSq_nonneg _
    have h0v : 0 ≤ energy v t := Complex.normSq_nonneg _
    have h0w : 0 ≤ energy w t := Complex.normSq_nonneg _
    show ‖ScertM M t * energy w t‖ ≤
      2 * ‖ScertM M t * energy G0 t‖ + 2 * ‖ScertM M t * energy v t‖
    rw [norm_mul, norm_mul, norm_mul, Real.norm_of_nonneg h0G, Real.norm_of_nonneg h0v,
      Real.norm_of_nonneg h0w]
    have := mul_le_mul_of_nonneg_left (energy_sub_le hG0i hvi t) (norm_nonneg (ScertM M t))
    linarith
  -- the three bounds
  have hcomp := complement_bound M L m s hsm B hsB hs0 H hHc hHi hFH hHs d j hcert hwi hCw hLT0
    hwsupp (by linarith) hwmom hEw hSw U hU hworth cf hR hT
  have hX := hcross c w ⟨hwi, ⟨_, hCw⟩, hwsupp, hwmom, hworth, hEw⟩
  have hl := hlow c
  have hdec : (fun u => v u + w u) = G0 := by
    funext u; simp only [hwdef]; ring
  rw [zero_quadratic_eq_energy g hm r a hw M (by linarith)]
  have e : (∫ t, ScertM M t * energy (Gm g) t) =
      ∫ t, ScertM M t * energy (fun u => v u + w u) t := by
    rw [hdec]
    congr 1; funext t; rw [hEG]
  rw [e, quad_add (ScertM M) (scertM_measurable M).aestronglyMeasurable hvi hwi (hSU c) hSw]
  exact mul_nonneg (by positivity)
    (feshbach_combine hcpos (integral_nonneg fun t => Complex.normSq_nonneg _) (hK c) hcomp hX hl)

end AEGIS.CvSWindowCertV1

#print axioms AEGIS.CvSWindowCertV1.exists_orth_coeffs
#print axioms AEGIS.CvSWindowCertV1.energy_translate
#print axioms AEGIS.CvSWindowCertV1.momentZero_translate
#print axioms AEGIS.CvSWindowCertV1.lowBlock_momentZero
#print axioms AEGIS.CvSWindowCertV1.energy_sub_le
#print axioms AEGIS.CvSWindowCertV1.window_of_certificate
