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

import WeilDiagonalLogGainS1V1
import WeilLogCorrelationL1V1

/-!
AEGIS Ω — the mean gain: S1 plus half the energy minus the mean (Claude Lab, 2026-11-22).

For `h : ℝ → ℂ` continuous, vanishing outside `[a, b]` (`w = b − a > 0`), with `E = ∫ ‖h‖²`, `M = ∫ h` and
`C(s) = ∫ h (x + s) · conj (h x) dx`,

  `(log 2 + 1/2) · E − ‖M‖² / (2w)  ≤  ∫_{(0, w]} (E − Re C(s)) / s ds`        (`mean_gain_lintegral`).

Split `1/s = 1/w + (1/s − 1/w)` on `(0, w]`:
* the `1/w` part is exact: `∫_{(0,w]} Re C = ‖M‖²/2` (`setIntegral_Ioc_reCorr`), because `Re C` is the sum of the
  autocorrelations of `Re h` and `Im h` (`WeilLogCorrelationL1V1.integral_autocorr_real`), is even, and vanishes
  beyond `w`;
* the `(1/s − 1/w)` part is bounded below as in S1, now with the column weights
  `log (w/(b−x)) − (x−a)/w` and `log (w/(x−a)) − (b−x)/w`, whose sum is at least `2 log 2 − 1`.

For a moment-zero packet `M` is tiny, so the diagonal gain rises from `log 2` (S1) to about `log 2 + 1/2`.
Abstract real analysis; not a statement about zeta; not RH.
-/

open MeasureTheory Set
open scoped ComplexConjugate ENNReal
set_option autoImplicit false
noncomputable section
namespace AEGIS.WeilDiagonalMeanGainV1

open AEGIS.WeilDiagonalLogGainS1V1
open AEGIS.WeilLogCorrelationL1V1

/-- `Re C(s)`. -/
def reCorr (h : ℝ → ℂ) (s : ℝ) : ℝ := (∫ x, h (x + s) * conj (h x)).re

theorem reCorr_eq (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ) (hs : ∀ x, x ∉ Icc a b → h x = 0)
    (s : ℝ) :
    reCorr h s = (∫ x, (h (x + s)).re * (h x).re) + ∫ x, (h (x + s)).im * (h x).im := by
  have hsh : Continuous (fun x => h (x + s)) := hc.comp (continuous_add_const s)
  have I4 : Integrable (fun x => h (x + s) * conj (h x)) :=
    integrable_of_zero_off _ (hsh.mul (Complex.continuous_conj.comp hc)) a b
      (fun x hx => by simp [hs x hx])
  have Ir : Integrable (fun x => (h (x + s)).re * (h x).re) :=
    integrable_of_zero_off _ ((Complex.continuous_re.comp hsh).mul (Complex.continuous_re.comp hc))
      a b (fun x hx => by simp [hs x hx])
  have Ii : Integrable (fun x => (h (x + s)).im * (h x).im) :=
    integrable_of_zero_off _ ((Complex.continuous_im.comp hsh).mul (Complex.continuous_im.comp hc))
      a b (fun x hx => by simp [hs x hx])
  have hre : (∫ x, h (x + s) * conj (h x)).re = ∫ x, (h (x + s) * conj (h x)).re := by
    have h' := Complex.reCLM.integral_comp_comm I4
    simpa using h'.symm
  unfold reCorr
  rw [hre, ← integral_add Ir Ii]
  congr 1
  funext x
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem integrable_re_of (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) : Integrable (fun x => (h x).re) :=
  integrable_of_zero_off _ (Complex.continuous_re.comp hc) a b (fun x hx => by simp [hs x hx])

theorem integrable_im_of (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) : Integrable (fun x => (h x).im) :=
  integrable_of_zero_off _ (Complex.continuous_im.comp hc) a b (fun x hx => by simp [hs x hx])

theorem integrable_reCorr (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) : Integrable (reCorr h) := by
  have e : reCorr h = fun s => (∫ x, (h (x + s)).re * (h x).re) + ∫ x, (h (x + s)).im * (h x).im :=
    funext (reCorr_eq h hc a b hs)
  rw [e]
  exact (integrable_autocorr _ (integrable_re_of h hc a b hs)).add
    (integrable_autocorr _ (integrable_im_of h hc a b hs))

theorem integral_reCorr (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) : ∫ s, reCorr h s = ‖∫ x, h x‖ ^ 2 := by
  have hr := integrable_re_of h hc a b hs
  have hi := integrable_im_of h hc a b hs
  have e : reCorr h = fun s => (∫ x, (h (x + s)).re * (h x).re) + ∫ x, (h (x + s)).im * (h x).im :=
    funext (reCorr_eq h hc a b hs)
  have hI : Integrable h := integrable_of_zero_off _ hc a b hs
  rw [e, integral_add (integrable_autocorr _ hr) (integrable_autocorr _ hi),
    integral_autocorr_real _ hr, integral_autocorr_real _ hi]
  have e1 : (∫ x, (h x).re) = (∫ x, h x).re := by
    have h' := Complex.reCLM.integral_comp_comm hI
    simpa using h'
  have e2 : (∫ x, (h x).im) = (∫ x, h x).im := by
    have h' := Complex.imCLM.integral_comp_comm hI
    simpa using h'
  rw [e1, e2, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem reCorr_neg (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) (s : ℝ) : reCorr h (-s) = reCorr h s := by
  have key : ∀ f : ℝ → ℝ, (∫ x, f (x + -s) * f x) = ∫ x, f (x + s) * f x := by
    intro f
    rw [← integral_add_right_eq_self (fun x => f (x + -s) * f x) s]
    congr 1
    funext x
    simp only [add_neg_cancel_right]
    ring
  rw [reCorr_eq h hc a b hs, reCorr_eq h hc a b hs, key (fun x => (h x).re), key (fun x => (h x).im)]

theorem reCorr_zero_of_gt (h : ℝ → ℂ) (a b : ℝ) (hs : ∀ x, x ∉ Icc a b → h x = 0)
    {s : ℝ} (hsw : b - a < s) : reCorr h s = 0 := by
  have hz : ∀ x, h (x + s) * conj (h x) = 0 := by
    intro x
    by_cases hx : x ∈ Icc a b
    · have h0 : h (x + s) = 0 := hs _ (fun hm => by linarith [hm.2, hx.1])
      simp [h0]
    · simp [hs x hx]
  unfold reCorr
  simp [hz]

/-- **`∫_{(0,w]} Re C = ‖M‖²/2`.** -/
theorem setIntegral_Ioc_reCorr (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ) (hab : a ≤ b)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) :
    ∫ s in Ioc (0 : ℝ) (b - a), reCorr h s = ‖∫ x, h x‖ ^ 2 / 2 := by
  have hI := integrable_reCorr h hc a b hs
  have hsplit := setIntegral_union (Iic_disjoint_Ioi (le_refl (0 : ℝ))) measurableSet_Ioi
    hI.integrableOn hI.integrableOn (f := reCorr h) (μ := volume)
  rw [Iic_union_Ioi, setIntegral_univ, integral_reCorr h hc a b hs] at hsplit
  have hneg : (∫ s in Iic (0 : ℝ), reCorr h s) = ∫ s in Ioi (0 : ℝ), reCorr h s := by
    have h1 := integral_comp_neg_Ioi (0 : ℝ) (reCorr h)
    rw [neg_zero] at h1
    rw [← h1]
    congr 1
    funext s
    exact reCorr_neg h hc a b hs s
  have htail : (∫ s in Ioi (0 : ℝ), reCorr h s) = ∫ s in Ioc (0 : ℝ) (b - a), reCorr h s := by
    rw [← Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ b - a),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hI.integrableOn hI.integrableOn]
    have h0 : (∫ s in Ioi (b - a), reCorr h s) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
        (fun s hs' => reCorr_zero_of_gt h a b hs hs')]
      simp
    rw [h0, add_zero]
  linarith

/-- The pointwise-row inequality of S1 without the `1/s` factor. -/
theorem row_key (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ) (hs : ∀ x, x ∉ Ioo a b → h x = 0)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ b - a) :
    ∫⁻ x, ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) ≤
      ENNReal.ofReal (2 * ((∫ x, ‖h x‖ ^ 2) - reCorr h s)) := by
  have hs' : ∀ x, x ∉ Icc a b → h x = 0 := fun x hx => hs x (fun h' => hx (Ioo_subset_Icc_self h'))
  have hA := sq_norm_sub_shift h hc a b hs' s
  have hz1 : ∀ x, x ∉ Icc (a - s) b → h (x + s) - h x = 0 := by
    intro x hx
    have a1 : h (x + s) = 0 := hs' _ (fun hm => hx ⟨by linarith [hm.1], by linarith [hm.2]⟩)
    have a2 : h x = 0 := hs' _ (fun hm => hx ⟨by linarith [hm.1], hm.2⟩)
    rw [a1, a2, sub_zero]
  have hintF : Integrable (fun x => ‖h (x + s) - h x‖ ^ 2) :=
    integrable_of_zero_off _ (((hc.comp (continuous_add_const s)).sub hc).norm.pow 2) (a - s) b
      (fun x hx => by simp [hz1 x hx])
  have hGm := sqG_measurable h hc
  have hm1 : Measurable (fun x : ℝ => if b - s < x then sqG h x else 0) :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id) hGm measurable_const
  unfold reCorr
  rw [← hA, ofReal_integral_eq_lintegral_ofReal hintF
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
  rw [lintegral_add_left hm1]
  have htr : ∫⁻ x, (if x < a + s then sqG h x else 0) =
      ∫⁻ x, (if x < a then sqG h (x + s) else 0) := by
    rw [← lintegral_add_right_eq_self (fun x => if x < a + s then sqG h x else 0) s]
    congr 1
    funext x
    by_cases hx : x < a
    · have hx' : x + s < a + s := by linarith
      simp only [if_pos hx, if_pos hx']
    · have hx' : ¬ (x + s < a + s) := not_lt.mpr (by linarith [not_lt.mp hx])
      simp only [if_neg hx, if_neg hx']
  rw [htr, ← lintegral_add_left hm1]
  apply lintegral_mono
  intro x
  exact pointwise_lower h a b hs s hs1 x

/-- `∫_{(c,w]} (1/s − 1/w) ds = log (w/c) − (w − c)/w`. -/
theorem lintegral_wt_Ioc (c w : ℝ) (hc : 0 < c) (hcw : c ≤ w) :
    ∫⁻ s in Ioc c w, ENNReal.ofReal (s⁻¹ - w⁻¹) =
      ENNReal.ofReal (Real.log (w / c) - (w - c) / w) := by
  have hw : 0 < w := lt_of_lt_of_le hc hcw
  have hco : ContinuousOn (fun s : ℝ => s⁻¹ - w⁻¹) (Icc c w) :=
    (continuousOn_inv₀.mono (fun s hs => (lt_of_lt_of_le hc hs.1).ne')).sub continuousOn_const
  have hint : IntegrableOn (fun s : ℝ => s⁻¹ - w⁻¹) (Ioc c w) :=
    (hco.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    have hii : IntervalIntegrable (fun s : ℝ => s⁻¹) volume c w :=
      (continuousOn_inv₀.mono (fun s hs => by
        rw [Set.uIcc_of_le hcw] at hs
        exact (lt_of_lt_of_le hc hs.1).ne')).intervalIntegrable
    rw [← intervalIntegral.integral_of_le hcw, intervalIntegral.integral_sub hii intervalIntegrable_const,
      integral_inv_of_pos hc hw, intervalIntegral.integral_const, smul_eq_mul]
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact sub_nonneg.mpr (inv_anti₀ (lt_trans hc hs.1) hs.2)

theorem wt_piece_nonneg (c w : ℝ) (hc : 0 < c) (hcw : c ≤ w) :
    0 ≤ Real.log (w / c) - (w - c) / w := by
  have hw : 0 < w := lt_of_lt_of_le hc hcw
  have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hw hc)
  have h2 : (w / c)⁻¹ = c / w := inv_div w c
  have h3 : (w - c) / w = 1 - c / w := by field_simp
  rw [h2] at h1
  linarith

/-- Weighted column: `∫_{(0,w]} (1/s − 1/w)(…) ds ≥ (2 log 2 − 1) ‖h x‖²`. -/
theorem column_wt (h : ℝ → ℂ) (a b : ℝ) (hab : a < b) (hs : ∀ x, x ∉ Ioo a b → h x = 0) (x : ℝ) :
    sqG h x * ENNReal.ofReal (2 * Real.log 2 - 1) ≤
      ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal (s⁻¹ - (b - a)⁻¹) *
        ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) := by
  by_cases hx : x ∈ Ioo a b
  · obtain ⟨hx0, hx1⟩ := hx
    have hfun : (fun s : ℝ => ENNReal.ofReal (s⁻¹ - (b - a)⁻¹) *
        ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0))) =
        fun s => sqG h x * ((Ioi (b - x)).indicator (fun s : ℝ => ENNReal.ofReal (s⁻¹ - (b - a)⁻¹)) s +
          (Ioi (x - a)).indicator (fun s : ℝ => ENNReal.ofReal (s⁻¹ - (b - a)⁻¹)) s) := by
      funext s
      have e1 : (b - s < x) ↔ (b - x < s) := ⟨fun h' => by linarith, fun h' => by linarith⟩
      have e2 : (x < a + s) ↔ (x - a < s) := ⟨fun h' => by linarith, fun h' => by linarith⟩
      simp only [Set.indicator_apply, mem_Ioi]
      by_cases c1 : b - x < s <;> by_cases c2 : x - a < s <;>
        simp only [e1, e2, c1, c2, if_true, if_false, add_zero, zero_add, mul_zero] <;>
        ring
    have hm : Measurable (fun s : ℝ => ENNReal.ofReal (s⁻¹ - (b - a)⁻¹)) :=
      (measurable_inv.sub_const _).ennreal_ofReal
    have hmsum : Measurable (fun s : ℝ =>
        (Ioi (b - x)).indicator (fun s : ℝ => ENNReal.ofReal (s⁻¹ - (b - a)⁻¹)) s +
        (Ioi (x - a)).indicator (fun s : ℝ => ENNReal.ofReal (s⁻¹ - (b - a)⁻¹)) s) :=
      (hm.indicator measurableSet_Ioi).add (hm.indicator measurableSet_Ioi)
    rw [hfun, lintegral_const_mul _ hmsum,
      lintegral_add_left (hm.indicator measurableSet_Ioi),
      lintegral_Ioc_indicator_Ioi (b - x) (b - a) (by linarith) _,
      lintegral_Ioc_indicator_Ioi (x - a) (b - a) (by linarith) _,
      lintegral_wt_Ioc (b - x) (b - a) (by linarith) (by linarith),
      lintegral_wt_Ioc (x - a) (b - a) (by linarith) (by linarith)]
    have n1 := wt_piece_nonneg (b - x) (b - a) (by linarith) (by linarith)
    have n2 := wt_piece_nonneg (x - a) (b - a) (by linarith) (by linarith)
    rw [← ENNReal.ofReal_add n1 n2]
    apply mul_le_mul_right
    apply ENNReal.ofReal_le_ofReal
    have hL := two_log_two_le a b x hx0 hx1
    have hlin : (b - a - (b - x)) / (b - a) + (b - a - (x - a)) / (b - a) = 1 := by
      rw [← add_div, div_eq_one_iff_eq (sub_pos.mpr hab).ne']
      ring
    linarith
  · simp [sqG, hs x hx]

/-- **Mean gain**, lower Lebesgue integral form. -/
theorem mean_gain_lintegral (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ) (hab : a < b)
    (hs : ∀ x, x ∉ Ioo a b → h x = 0) :
    ENNReal.ofReal ((Real.log 2 + 1 / 2) * (∫ x, ‖h x‖ ^ 2) - ‖∫ x, h x‖ ^ 2 / (2 * (b - a))) ≤
      ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal
        (((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s) := by
  have hw : 0 < b - a := by linarith
  have hs' : ∀ x, x ∉ Icc a b → h x = 0 := fun x hx => hs x (fun h' => hx (Ioo_subset_Icc_self h'))
  set E := ∫ x, ‖h x‖ ^ 2 with hEdef
  have hGm := sqG_measurable h hc
  have hint2 : Integrable (fun x => ‖h x‖ ^ 2) :=
    integrable_of_zero_off _ (hc.norm.pow 2) a b (fun x hx => by simp [hs' x hx])
  have hEl : ENNReal.ofReal E = ∫⁻ x, sqG h x :=
    ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall (fun x => sq_nonneg ‖h x‖))
  have hE0 : 0 ≤ E := integral_nonneg (fun x => sq_nonneg _)
  have hR := integrable_reCorr h hc a b hs'
  have hdiff : ∀ s, 0 ≤ E - reCorr h s := by
    intro s
    have hA := sq_norm_sub_shift h hc a b hs' s
    have h0 : 0 ≤ ∫ x, ‖h (x + s) - h x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    unfold reCorr
    linarith
  -- split `1/s = 1/w + (1/s − 1/w)`
  have hsplit : ∀ s ∈ Ioc (0 : ℝ) (b - a),
      ENNReal.ofReal ((E - (∫ x, h (x + s) * conj (h x)).re) / s) =
        ENNReal.ofReal ((E - reCorr h s) / (b - a)) +
          ENNReal.ofReal ((s⁻¹ - (b - a)⁻¹) * (E - reCorr h s)) := by
    intro s hs01
    have hwt : 0 ≤ s⁻¹ - (b - a)⁻¹ := sub_nonneg.mpr (inv_anti₀ hs01.1 hs01.2)
    rw [← ENNReal.ofReal_add (div_nonneg (hdiff s) hw.le) (mul_nonneg hwt (hdiff s))]
    congr 1
    unfold reCorr
    field_simp
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioc hsplit]
  have hmeas1 : AEMeasurable (fun s => ENNReal.ofReal ((E - reCorr h s) / (b - a)))
      (volume.restrict (Ioc (0 : ℝ) (b - a))) :=
    (((aestronglyMeasurable_const.sub hR.aestronglyMeasurable).aemeasurable.div_const
      (b - a)).ennreal_ofReal).restrict
  rw [lintegral_add_left' hmeas1]
  -- first part, exact
  have hfirst : ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal ((E - reCorr h s) / (b - a)) =
      ENNReal.ofReal (E - ‖∫ x, h x‖ ^ 2 / (2 * (b - a))) := by
    have hi : IntegrableOn (fun s => (E - reCorr h s) / (b - a)) (Ioc (0 : ℝ) (b - a)) :=
      ((continuous_const.integrableOn_Ioc).sub hR.integrableOn).div_const _
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (by filter_upwards [] with s; exact div_nonneg (hdiff s) hw.le)]
    congr 1
    have e1 : (∫ s in Ioc (0 : ℝ) (b - a), (E - reCorr h s) / (b - a)) =
        (∫ s in Ioc (0 : ℝ) (b - a), (E - reCorr h s)) / (b - a) := integral_div _ _
    have e2 : (∫ s in Ioc (0 : ℝ) (b - a), (E - reCorr h s)) =
        (∫ _s in Ioc (0 : ℝ) (b - a), E) - ∫ s in Ioc (0 : ℝ) (b - a), reCorr h s :=
      integral_sub (continuous_const.integrableOn_Ioc) hR.integrableOn
    have e3 : (∫ _s in Ioc (0 : ℝ) (b - a), E) = (b - a) * E := by
      rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hw.le]
      ring
    rw [e1, e2, e3, setIntegral_Ioc_reCorr h hc a b hab.le hs']
    field_simp
  -- second part, weighted columns
  have hsecond : ENNReal.ofReal ((Real.log 2 - 1 / 2) * E) ≤
      ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal ((s⁻¹ - (b - a)⁻¹) * (E - reCorr h s)) := by
    have hΦm : Measurable (Function.uncurry fun (s x : ℝ) => ENNReal.ofReal (s⁻¹ - (b - a)⁻¹) *
        ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0))) := by
      change Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1⁻¹ - (b - a)⁻¹) *
        ((if b - p.1 < p.2 then sqG h p.2 else 0) + (if p.2 < a + p.1 then sqG h p.2 else 0)))
      refine ((measurable_fst.inv.sub_const _).ennreal_ofReal).mul (Measurable.add ?_ ?_)
      · exact Measurable.ite (measurableSet_lt (measurable_const.sub measurable_fst) measurable_snd)
          (hGm.comp measurable_snd) measurable_const
      · exact Measurable.ite (measurableSet_lt measurable_snd (measurable_const.add measurable_fst))
          (hGm.comp measurable_snd) measurable_const
    have hswap := lintegral_lintegral_swap (μ := volume.restrict (Ioc (0 : ℝ) (b - a)))
      (ν := (volume : Measure ℝ)) hΦm.aemeasurable
    have hupper : ∀ s ∈ Ioc (0 : ℝ) (b - a),
        ∫⁻ x, ENNReal.ofReal (s⁻¹ - (b - a)⁻¹) *
            ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) ≤
          2 * ENNReal.ofReal ((s⁻¹ - (b - a)⁻¹) * (E - reCorr h s)) := by
      intro s hs01
      have hwt : 0 ≤ s⁻¹ - (b - a)⁻¹ := sub_nonneg.mpr (inv_anti₀ hs01.1 hs01.2)
      have hm1 : Measurable (fun x : ℝ => if b - s < x then sqG h x else 0) :=
        Measurable.ite (measurableSet_lt measurable_const measurable_id) hGm measurable_const
      have hm2 : Measurable (fun x : ℝ => if x < a + s then sqG h x else 0) :=
        Measurable.ite (measurableSet_lt measurable_id measurable_const) hGm measurable_const
      have hm12 : Measurable (fun x : ℝ =>
          (if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) := hm1.add hm2
      rw [lintegral_const_mul _ hm12]
      calc ENNReal.ofReal (s⁻¹ - (b - a)⁻¹) *
            ∫⁻ x, ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0))
          ≤ ENNReal.ofReal (s⁻¹ - (b - a)⁻¹) * ENNReal.ofReal (2 * (E - reCorr h s)) :=
            mul_le_mul_right (row_key h hc a b hs s hs01.1 hs01.2) _
        _ = 2 * ENNReal.ofReal ((s⁻¹ - (b - a)⁻¹) * (E - reCorr h s)) := by
            rw [← ENNReal.ofReal_mul hwt, ← ENNReal.ofReal_ofNat 2,
              ← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            ring
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal ((Real.log 2 - 1 / 2) * E) ≤
        2 * ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal ((s⁻¹ - (b - a)⁻¹) * (E - reCorr h s)) := by
      calc (2 : ℝ≥0∞) * ENNReal.ofReal ((Real.log 2 - 1 / 2) * E)
          = ∫⁻ x, sqG h x * ENNReal.ofReal (2 * Real.log 2 - 1) := by
            rw [lintegral_mul_const _ hGm, ← hEl, ← ENNReal.ofReal_mul hE0, ← ENNReal.ofReal_ofNat 2,
              ← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            ring
        _ ≤ ∫⁻ x, ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal (s⁻¹ - (b - a)⁻¹) *
              ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) :=
            lintegral_mono (fun x => column_wt h a b hab hs x)
        _ = ∫⁻ s in Ioc (0 : ℝ) (b - a), ∫⁻ x, ENNReal.ofReal (s⁻¹ - (b - a)⁻¹) *
              ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) := hswap.symm
        _ ≤ ∫⁻ s in Ioc (0 : ℝ) (b - a), 2 * ENNReal.ofReal ((s⁻¹ - (b - a)⁻¹) * (E - reCorr h s)) :=
            setLIntegral_mono' measurableSet_Ioc hupper
        _ = 2 * ∫⁻ s in Ioc (0 : ℝ) (b - a),
              ENNReal.ofReal ((s⁻¹ - (b - a)⁻¹) * (E - reCorr h s)) :=
            lintegral_const_mul' _ _ (by simp)
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by simp)).mp h2
  rw [hfirst]
  calc ENNReal.ofReal ((Real.log 2 + 1 / 2) * E - ‖∫ x, h x‖ ^ 2 / (2 * (b - a)))
      = ENNReal.ofReal ((E - ‖∫ x, h x‖ ^ 2 / (2 * (b - a))) + (Real.log 2 - 1 / 2) * E) := by
        congr 1
        ring
    _ ≤ ENNReal.ofReal (E - ‖∫ x, h x‖ ^ 2 / (2 * (b - a))) +
          ENNReal.ofReal ((Real.log 2 - 1 / 2) * E) := ENNReal.ofReal_add_le
    _ ≤ _ := add_le_add (le_refl _) hsecond

end AEGIS.WeilDiagonalMeanGainV1

#print axioms AEGIS.WeilDiagonalMeanGainV1.setIntegral_Ioc_reCorr
#print axioms AEGIS.WeilDiagonalMeanGainV1.mean_gain_lintegral
