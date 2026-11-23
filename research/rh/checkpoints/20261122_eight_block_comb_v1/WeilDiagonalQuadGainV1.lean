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

import WeilDiagonalMeanGainV1

/-!
AEGIS Ω — the quadratic gain `log 2 + 4/3` (Claude Lab, 2026-11-22).

`WeilDiagonalMeanGainV1` splits `1/s = 1/w + (1/s − 1/w)`. Here the constant `1/w` is replaced by the quadratic
`p(s) = (3 − 4 (s/w)²)/w`, which still satisfies `p(s) ≤ 1/s` on `(0, w]` because
`1 − 3u + 4u³ = (2u − 1)² (u + 1) ≥ 0`. For `h` continuous, vanishing outside `[a, b]`, `w = b − a`:

* the `p` part is exact (`setIntegral_Ioc_p_part`): `(5/3) E − 3 ‖M‖²/(2w) + 4 Q/w³`, where
  `Q = ∫_{(0,w]} s² Re C(s) ds` is given by the second-moment identity
  `∫ s² A(s) ds = 2 (∫ (x−c)² a)(∫ a) − 2 (∫ (x−c) a)²` for autocorrelations of real functions
  (`integral_sq_autocorr`, Fubini);
* the `(1/s − p)` part is the S1 column argument with weights summing to `−log P + 4P − 5/3 ≥ 2 log 2 − 2/3`,
  `P = (b−x)(x−a)/w²` (`column_wt2`), contributing `(log 2 − 1/3) E`.

Hence (`quad_gain`, Bochner form, when the right side is integrable)

  `(log 2 + 4/3) E − 3 ‖M‖²/(2w) + 4 Q/w³  ≤  ∫_{(0,w]} (E − Re C(s))/s ds`.

For moment-zero packets `M` and the first moment are tiny, so `Q ≈ 0` and the gain is about `log 2 + 4/3`.
Abstract real analysis; not RH.
-/

open MeasureTheory Set
open scoped ComplexConjugate ENNReal
set_option autoImplicit false
noncomputable section
namespace AEGIS.WeilDiagonalQuadGainV1

open AEGIS.WeilDiagonalLogGainS1V1
open AEGIS.WeilDiagonalMeanGainV1

theorem prod_integrable (a : ℝ → ℝ) (ha : Continuous a) (lo hi : ℝ)
    (hs : ∀ x, x ∉ Icc lo hi → a x = 0) :
    Integrable (Function.uncurry fun (s v : ℝ) => s ^ 2 * (a (v + s) * a v)) (volume.prod volume) := by
  have hc : Continuous (Function.uncurry fun (s v : ℝ) => s ^ 2 * (a (v + s) * a v)) := by
    change Continuous (fun z : ℝ × ℝ => z.1 ^ 2 * (a (z.2 + z.1) * a z.2))
    exact (continuous_fst.pow 2).mul ((ha.comp (continuous_snd.add continuous_fst)).mul
      (ha.comp continuous_snd))
  have hk : HasCompactSupport (Function.uncurry fun (s v : ℝ) => s ^ 2 * (a (v + s) * a v)) := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_Icc : IsCompact (Icc (lo - hi) (hi - lo))).prod (isCompact_Icc : IsCompact (Icc lo hi)))
    intro z hz
    have h1 : a (z.2 + z.1) ≠ 0 := by
      intro h
      apply hz
      show z.1 ^ 2 * (a (z.2 + z.1) * a z.2) = 0
      rw [h]
      ring
    have h2 : a z.2 ≠ 0 := by
      intro h
      apply hz
      show z.1 ^ 2 * (a (z.2 + z.1) * a z.2) = 0
      rw [h]
      ring
    have hI1 : z.2 + z.1 ∈ Icc lo hi := by
      by_contra hn
      exact h1 (hs _ hn)
    have hI2 : z.2 ∈ Icc lo hi := by
      by_contra hn
      exact h2 (hs _ hn)
    exact ⟨⟨by linarith [hI1.1, hI2.2], by linarith [hI1.2, hI2.1]⟩, hI2⟩
  exact hc.integrable_of_hasCompactSupport hk

theorem integrable_sq_autocorr (a : ℝ → ℝ) (ha : Continuous a) (lo hi : ℝ)
    (hs : ∀ x, x ∉ Icc lo hi → a x = 0) :
    Integrable (fun s => s ^ 2 * ∫ v, a (v + s) * a v) := by
  have hi := (prod_integrable a ha lo hi hs).integral_prod_left
  simpa only [Function.uncurry_apply_pair, integral_const_mul] using hi

theorem integrable_pow_mul (a : ℝ → ℝ) (ha : Continuous a) (lo hi : ℝ)
    (hs : ∀ x, x ∉ Icc lo hi → a x = 0) (c : ℝ) (k : ℕ) :
    Integrable (fun x => (x - c) ^ k * a x) :=
  integrable_of_zero_off _ (((continuous_id.sub continuous_const).pow k).mul ha) lo hi
    (fun x hx => by simp [hs x hx])

/-- **Second-moment identity** for the autocorrelation of a real function. -/
theorem integral_sq_autocorr (a : ℝ → ℝ) (ha : Continuous a) (lo hi : ℝ)
    (hs : ∀ x, x ∉ Icc lo hi → a x = 0) (c : ℝ) :
    ∫ s, s ^ 2 * ∫ v, a (v + s) * a v =
      2 * (∫ x, (x - c) ^ 2 * a x) * (∫ x, a x) - 2 * (∫ x, (x - c) * a x) ^ 2 := by
  have hF := prod_integrable a ha lo hi hs
  have I0 : Integrable a := integrable_of_zero_off _ ha lo hi hs
  have I1 : Integrable (fun x => (x - c) * a x) :=
    integrable_of_zero_off _ ((continuous_id.sub continuous_const).mul ha) lo hi
      (fun x hx => by simp [hs x hx])
  have I2 : Integrable (fun x => (x - c) ^ 2 * a x) := integrable_pow_mul a ha lo hi hs c 2
  have hinner : ∀ v, (∫ s, s ^ 2 * a (v + s)) =
      (∫ x, (x - c) ^ 2 * a x) - 2 * (v - c) * (∫ x, (x - c) * a x) + (v - c) ^ 2 * (∫ x, a x) := by
    intro v
    have hsh : (∫ s, s ^ 2 * a (v + s)) = ∫ y, (y - v) ^ 2 * a y := by
      rw [← integral_add_right_eq_self (fun y => (y - v) ^ 2 * a y) v]
      congr 1
      funext s
      rw [add_sub_cancel_right, add_comm]
    have hexp : (fun y => (y - v) ^ 2 * a y) =
        fun y => (y - c) ^ 2 * a y - 2 * (v - c) * ((y - c) * a y) + (v - c) ^ 2 * a y := by
      funext y
      ring
    have Ia : Integrable (fun y => (y - c) ^ 2 * a y - 2 * (v - c) * ((y - c) * a y)) :=
      I2.sub (I1.const_mul _)
    have Ib : Integrable (fun y => (v - c) ^ 2 * a y) := I0.const_mul _
    have Ic : Integrable (fun y => 2 * (v - c) * ((y - c) * a y)) := I1.const_mul _
    have e1 : (∫ y, ((y - c) ^ 2 * a y - 2 * (v - c) * ((y - c) * a y) + (v - c) ^ 2 * a y)) =
        (∫ y, ((y - c) ^ 2 * a y - 2 * (v - c) * ((y - c) * a y))) + ∫ y, (v - c) ^ 2 * a y :=
      integral_add Ia Ib
    have e2 : (∫ y, ((y - c) ^ 2 * a y - 2 * (v - c) * ((y - c) * a y))) =
        (∫ y, (y - c) ^ 2 * a y) - ∫ y, 2 * (v - c) * ((y - c) * a y) := integral_sub I2 Ic
    have e3 : (∫ y, 2 * (v - c) * ((y - c) * a y)) = 2 * (v - c) * ∫ y, (y - c) * a y :=
      integral_const_mul _ _
    have e4 : (∫ y, (v - c) ^ 2 * a y) = (v - c) ^ 2 * ∫ y, a y := integral_const_mul _ _
    rw [hsh, hexp, e1, e2, e3, e4]
  have Ja : Integrable (fun v => (∫ x, (x - c) ^ 2 * a x) * a v -
      (2 * (∫ x, (x - c) * a x)) * ((v - c) * a v)) := (I0.const_mul _).sub (I1.const_mul _)
  have Jb : Integrable (fun v => (∫ x, a x) * ((v - c) ^ 2 * a v)) := I2.const_mul _
  have f1 : (∫ v, ((∫ x, (x - c) ^ 2 * a x) * a v - (2 * (∫ x, (x - c) * a x)) * ((v - c) * a v) +
      (∫ x, a x) * ((v - c) ^ 2 * a v))) =
      (∫ v, ((∫ x, (x - c) ^ 2 * a x) * a v - (2 * (∫ x, (x - c) * a x)) * ((v - c) * a v))) +
        ∫ v, (∫ x, a x) * ((v - c) ^ 2 * a v) := integral_add Ja Jb
  have f2 : (∫ v, ((∫ x, (x - c) ^ 2 * a x) * a v - (2 * (∫ x, (x - c) * a x)) * ((v - c) * a v))) =
      (∫ v, (∫ x, (x - c) ^ 2 * a x) * a v) - ∫ v, (2 * (∫ x, (x - c) * a x)) * ((v - c) * a v) :=
    integral_sub (I0.const_mul _) (I1.const_mul _)
  have f3 : (∫ v, (∫ x, (x - c) ^ 2 * a x) * a v) = (∫ x, (x - c) ^ 2 * a x) * ∫ v, a v :=
    integral_const_mul _ _
  have f4 : (∫ v, (2 * (∫ x, (x - c) * a x)) * ((v - c) * a v)) =
      (2 * (∫ x, (x - c) * a x)) * ∫ v, (v - c) * a v := integral_const_mul _ _
  have f5 : (∫ v, (∫ x, a x) * ((v - c) ^ 2 * a v)) = (∫ x, a x) * ∫ v, (v - c) ^ 2 * a v :=
    integral_const_mul _ _
  calc ∫ s, s ^ 2 * ∫ v, a (v + s) * a v
      = ∫ s, ∫ v, s ^ 2 * (a (v + s) * a v) := by
        congr 1
        funext s
        rw [integral_const_mul]
    _ = ∫ v, ∫ s, s ^ 2 * (a (v + s) * a v) := integral_integral_swap hF
    _ = ∫ v, ((∫ x, (x - c) ^ 2 * a x) * a v - (2 * (∫ x, (x - c) * a x)) * ((v - c) * a v) +
          (∫ x, a x) * ((v - c) ^ 2 * a v)) := by
        congr 1
        funext v
        have e : (∫ s, s ^ 2 * (a (v + s) * a v)) = (∫ s, s ^ 2 * a (v + s)) * a v := by
          rw [← integral_mul_const]
          congr 1
          funext s
          ring
        rw [e, hinner v]
        ring
    _ = 2 * (∫ x, (x - c) ^ 2 * a x) * (∫ x, a x) - 2 * (∫ x, (x - c) * a x) ^ 2 := by
        rw [f1, f2, f3, f4, f5]
        ring

/-- The real quantity `Q` of the second-moment identity for `h : ℝ → ℂ`, centre `c`. -/
def qMom (h : ℝ → ℂ) (c : ℝ) : ℝ :=
  ((∫ x, (x - c) ^ 2 * (h x).re) * (∫ x, (h x).re) - (∫ x, (x - c) * (h x).re) ^ 2) +
  ((∫ x, (x - c) ^ 2 * (h x).im) * (∫ x, (h x).im) - (∫ x, (x - c) * (h x).im) ^ 2)

theorem integrable_sq_reCorr (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) : Integrable (fun s => s ^ 2 * reCorr h s) := by
  have e : (fun s => s ^ 2 * reCorr h s) = fun s =>
      s ^ 2 * (∫ x, (h (x + s)).re * (h x).re) + s ^ 2 * ∫ x, (h (x + s)).im * (h x).im := by
    funext s
    rw [reCorr_eq h hc a b hs, mul_add]
  rw [e]
  exact (integrable_sq_autocorr (fun x => (h x).re) (Complex.continuous_re.comp hc) a b
      (fun x hx => by simp [hs x hx])).add
    (integrable_sq_autocorr (fun x => (h x).im) (Complex.continuous_im.comp hc) a b
      (fun x hx => by simp [hs x hx]))

theorem integral_sq_reCorr (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) (c : ℝ) : ∫ s, s ^ 2 * reCorr h s = 2 * qMom h c := by
  have hr : ∀ x, x ∉ Icc a b → (h x).re = 0 := fun x hx => by simp [hs x hx]
  have hi : ∀ x, x ∉ Icc a b → (h x).im = 0 := fun x hx => by simp [hs x hx]
  have e : (fun s => s ^ 2 * reCorr h s) = fun s =>
      s ^ 2 * (∫ x, (h (x + s)).re * (h x).re) + s ^ 2 * ∫ x, (h (x + s)).im * (h x).im := by
    funext s
    rw [reCorr_eq h hc a b hs, mul_add]
  rw [e, integral_add (integrable_sq_autocorr (fun x => (h x).re) (Complex.continuous_re.comp hc) a b hr)
      (integrable_sq_autocorr (fun x => (h x).im) (Complex.continuous_im.comp hc) a b hi),
    integral_sq_autocorr (fun x => (h x).re) (Complex.continuous_re.comp hc) a b hr c,
    integral_sq_autocorr (fun x => (h x).im) (Complex.continuous_im.comp hc) a b hi c]
  unfold qMom
  ring

/-- Half-line integral of an even function supported in `[−w, w]`. -/
theorem setIntegral_Ioc_of_even (f : ℝ → ℝ) (hI : Integrable f) (heven : ∀ s, f (-s) = f s)
    (w : ℝ) (hw : 0 ≤ w) (hzero : ∀ s, w < s → f s = 0) :
    ∫ s in Ioc (0 : ℝ) w, f s = (∫ s, f s) / 2 := by
  have hsplit := setIntegral_union (Iic_disjoint_Ioi (le_refl (0 : ℝ))) measurableSet_Ioi
    hI.integrableOn hI.integrableOn (f := f) (μ := volume)
  rw [Iic_union_Ioi, setIntegral_univ] at hsplit
  have hneg : (∫ s in Iic (0 : ℝ), f s) = ∫ s in Ioi (0 : ℝ), f s := by
    have h1 := integral_comp_neg_Ioi (0 : ℝ) f
    rw [neg_zero] at h1
    rw [← h1]
    congr 1
    funext s
    exact heven s
  have htail : (∫ s in Ioi (0 : ℝ), f s) = ∫ s in Ioc (0 : ℝ) w, f s := by
    rw [← Ioc_union_Ioi_eq_Ioi hw,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hI.integrableOn hI.integrableOn]
    have h0 : (∫ s in Ioi w, f s) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ)) (fun s hs' => hzero s hs')]
      simp
    rw [h0, add_zero]
  linarith

theorem setIntegral_Ioc_sq_reCorr (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ) (hab : a ≤ b)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) (c : ℝ) :
    ∫ s in Ioc (0 : ℝ) (b - a), s ^ 2 * reCorr h s = qMom h c := by
  rw [setIntegral_Ioc_of_even _ (integrable_sq_reCorr h hc a b hs)
    (fun s => by rw [reCorr_neg h hc a b hs, neg_sq]) (b - a) (by linarith)
    (fun s hs' => by rw [reCorr_zero_of_gt h a b hs hs', mul_zero]),
    integral_sq_reCorr h hc a b hs c]
  ring

/-- The weight `1/s − p(s) = 1/s − 3/w + 4 s²/w³`, nonnegative on `(0, w]`. -/
def wt2 (w s : ℝ) : ℝ := s⁻¹ - 3 / w + 4 * s ^ 2 / w ^ 3

theorem wt2_nonneg (w s : ℝ) (hs : 0 < s) (hw : 0 < w) : 0 ≤ wt2 w s := by
  unfold wt2
  have key : s⁻¹ - 3 / w + 4 * s ^ 2 / w ^ 3 = (w - 2 * s) ^ 2 * (w + s) / (s * w ^ 3) := by
    field_simp
    ring
  rw [key]
  positivity

theorem integrableOn_wt2 (c w : ℝ) (hc : 0 < c) :
    IntegrableOn (fun s : ℝ => wt2 w s) (Ioc c w) := by
  have hco : ContinuousOn (fun s : ℝ => wt2 w s) (Icc c w) := by
    unfold wt2
    exact ((continuousOn_inv₀.mono (fun s hs => (lt_of_lt_of_le hc hs.1).ne')).sub continuousOn_const).add
      (((continuous_const.mul (continuous_id.pow 2)).div_const _).continuousOn)
  exact (hco.integrableOn_Icc).mono_set Ioc_subset_Icc_self

theorem integral_wt2_Ioc (c w : ℝ) (hc : 0 < c) (hcw : c ≤ w) :
    ∫ s in Ioc c w, wt2 w s =
      Real.log (w / c) - 3 * (w - c) / w + 4 * (w ^ 3 - c ^ 3) / (3 * w ^ 3) := by
  have hw : 0 < w := lt_of_lt_of_le hc hcw
  have hii : IntervalIntegrable (fun s : ℝ => s⁻¹) volume c w :=
    (continuousOn_inv₀.mono (fun s hs => by
      rw [Set.uIcc_of_le hcw] at hs
      exact (lt_of_lt_of_le hc hs.1).ne')).intervalIntegrable
  have hpi : IntervalIntegrable (fun s : ℝ => 4 * s ^ 2 / w ^ 3) volume c w :=
    ((continuous_const.mul (continuous_id.pow 2)).div_const _).intervalIntegrable _ _
  unfold wt2
  rw [← intervalIntegral.integral_of_le hcw,
    intervalIntegral.integral_add (hii.sub intervalIntegrable_const) hpi,
    intervalIntegral.integral_sub hii intervalIntegrable_const,
    integral_inv_of_pos hc hw, intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
  field_simp
  ring

theorem lintegral_wt2_Ioc (c w : ℝ) (hc : 0 < c) (hcw : c ≤ w) :
    ∫⁻ s in Ioc c w, ENNReal.ofReal (wt2 w s) =
      ENNReal.ofReal (Real.log (w / c) - 3 * (w - c) / w + 4 * (w ^ 3 - c ^ 3) / (3 * w ^ 3)) := by
  have hw : 0 < w := lt_of_lt_of_le hc hcw
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_wt2 c w hc), integral_wt2_Ioc c w hc hcw]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact wt2_nonneg w s (lt_trans hc hs.1) hw

theorem wt2_piece_nonneg (c w : ℝ) (hc : 0 < c) (hcw : c ≤ w) :
    0 ≤ Real.log (w / c) - 3 * (w - c) / w + 4 * (w ^ 3 - c ^ 3) / (3 * w ^ 3) := by
  have hw : 0 < w := lt_of_lt_of_le hc hcw
  rw [← integral_wt2_Ioc c w hc hcw]
  exact setIntegral_nonneg measurableSet_Ioc (fun s hs => wt2_nonneg w s (lt_trans hc hs.1) hw)

/-- Weighted column with `wt2`: at least `(2 log 2 − 2/3) ‖h x‖²`. -/
theorem column_wt2 (h : ℝ → ℂ) (a b : ℝ) (hab : a < b) (hs : ∀ x, x ∉ Ioo a b → h x = 0) (x : ℝ) :
    sqG h x * ENNReal.ofReal (2 * Real.log 2 - 2 / 3) ≤
      ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal (wt2 (b - a) s) *
        ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) := by
  by_cases hx : x ∈ Ioo a b
  · obtain ⟨hx0, hx1⟩ := hx
    have hfun : (fun s : ℝ => ENNReal.ofReal (wt2 (b - a) s) *
        ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0))) =
        fun s => sqG h x * ((Ioi (b - x)).indicator (fun s : ℝ => ENNReal.ofReal (wt2 (b - a) s)) s +
          (Ioi (x - a)).indicator (fun s : ℝ => ENNReal.ofReal (wt2 (b - a) s)) s) := by
      funext s
      have e1 : (b - s < x) ↔ (b - x < s) := ⟨fun h' => by linarith, fun h' => by linarith⟩
      have e2 : (x < a + s) ↔ (x - a < s) := ⟨fun h' => by linarith, fun h' => by linarith⟩
      simp only [Set.indicator_apply, mem_Ioi]
      by_cases c1 : b - x < s <;> by_cases c2 : x - a < s <;>
        simp only [e1, e2, c1, c2, if_true, if_false, add_zero, zero_add, mul_zero] <;>
        ring
    have hm : Measurable (fun s : ℝ => ENNReal.ofReal (wt2 (b - a) s)) := by
      unfold wt2
      exact (((measurable_inv.sub_const _).add
        ((measurable_const.mul (measurable_id.pow_const 2)).div_const _))).ennreal_ofReal
    have hmsum : Measurable (fun s : ℝ =>
        (Ioi (b - x)).indicator (fun s : ℝ => ENNReal.ofReal (wt2 (b - a) s)) s +
        (Ioi (x - a)).indicator (fun s : ℝ => ENNReal.ofReal (wt2 (b - a) s)) s) :=
      (hm.indicator measurableSet_Ioi).add (hm.indicator measurableSet_Ioi)
    rw [hfun, lintegral_const_mul _ hmsum,
      lintegral_add_left (hm.indicator measurableSet_Ioi),
      lintegral_Ioc_indicator_Ioi (b - x) (b - a) (by linarith) _,
      lintegral_Ioc_indicator_Ioi (x - a) (b - a) (by linarith) _,
      lintegral_wt2_Ioc (b - x) (b - a) (by linarith) (by linarith),
      lintegral_wt2_Ioc (x - a) (b - a) (by linarith) (by linarith)]
    have n1 := wt2_piece_nonneg (b - x) (b - a) (by linarith) (by linarith)
    have n2 := wt2_piece_nonneg (x - a) (b - a) (by linarith) (by linarith)
    rw [← ENNReal.ofReal_add n1 n2]
    apply mul_le_mul_right
    apply ENNReal.ofReal_le_ofReal
    have hw : 0 < b - a := by linarith
    have p1 : 0 < b - x := by linarith
    have p2 : 0 < x - a := by linarith
    -- log part: log(w/c1) + log(w/c2) ≥ 2 log 2 + 1 − 4 c1 c2 / w²
    have hy : 0 < (b - a) ^ 2 / (4 * ((b - x) * (x - a))) := by positivity
    have hlog := Real.one_sub_inv_le_log_of_pos hy
    have hsplitlog : Real.log ((b - a) ^ 2 / (4 * ((b - x) * (x - a)))) =
        Real.log ((b - a) / (b - x)) + Real.log ((b - a) / (x - a)) - 2 * Real.log 2 := by
      have e4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      rw [show (b - a) ^ 2 / (4 * ((b - x) * (x - a))) =
          ((b - a) / (b - x)) * ((b - a) / (x - a)) / 4 by field_simp,
        Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity), e4]
    have hinv : ((b - a) ^ 2 / (4 * ((b - x) * (x - a))))⁻¹ = 4 * ((b - x) * (x - a)) / (b - a) ^ 2 :=
      inv_div _ _
    rw [hsplitlog, hinv] at hlog
    have hpoly : -(3 * (b - a - (b - x)) / (b - a)) + 4 * ((b - a) ^ 3 - (b - x) ^ 3) / (3 * (b - a) ^ 3) +
        (-(3 * (b - a - (x - a)) / (b - a)) + 4 * ((b - a) ^ 3 - (x - a) ^ 3) / (3 * (b - a) ^ 3)) =
        4 * ((b - x) * (x - a)) / (b - a) ^ 2 - 5 / 3 := by
      field_simp
      ring
    linarith [hlog, hpoly]
  · simp [sqG, hs x hx]

/-- The `p`-part, exact. -/
theorem setIntegral_Ioc_p_part (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ) (hab : a < b)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) :
    ∫ s in Ioc (0 : ℝ) (b - a), (3 / (b - a) - 4 * s ^ 2 / (b - a) ^ 3) *
        ((∫ x, ‖h x‖ ^ 2) - reCorr h s) =
      (5 / 3) * (∫ x, ‖h x‖ ^ 2) - 3 * ‖∫ x, h x‖ ^ 2 / (2 * (b - a)) + 4 * qMom h a / (b - a) ^ 3 := by
  have hw : 0 < b - a := by linarith
  set E := ∫ x, ‖h x‖ ^ 2
  have hR := integrable_reCorr h hc a b hs
  have hR2 := integrable_sq_reCorr h hc a b hs
  have hexp : (fun s => (3 / (b - a) - 4 * s ^ 2 / (b - a) ^ 3) * (E - reCorr h s)) =
      fun s => (3 / (b - a) * E - 4 * E / (b - a) ^ 3 * s ^ 2) -
        (3 / (b - a) * reCorr h s - 4 / (b - a) ^ 3 * (s ^ 2 * reCorr h s)) := by
    funext s
    ring
  have Ipoly : IntegrableOn (fun s : ℝ => 3 / (b - a) * E - 4 * E / (b - a) ^ 3 * s ^ 2) (Ioc (0 : ℝ) (b - a)) :=
    (continuous_const.sub (continuous_const.mul (continuous_id.pow 2))).integrableOn_Ioc
  have Icorr : IntegrableOn (fun s => 3 / (b - a) * reCorr h s - 4 / (b - a) ^ 3 * (s ^ 2 * reCorr h s))
      (Ioc (0 : ℝ) (b - a)) :=
    ((hR.const_mul _).sub (hR2.const_mul _)).integrableOn
  have Iconst : IntegrableOn (fun _ : ℝ => 3 / (b - a) * E) (Ioc (0 : ℝ) (b - a)) :=
    continuous_const.integrableOn_Ioc
  have Isq : IntegrableOn (fun s : ℝ => 4 * E / (b - a) ^ 3 * s ^ 2) (Ioc (0 : ℝ) (b - a)) :=
    (continuous_const.mul (continuous_id.pow 2)).integrableOn_Ioc
  have IR1 : IntegrableOn (fun s => 3 / (b - a) * reCorr h s) (Ioc (0 : ℝ) (b - a)) :=
    (hR.const_mul _).integrableOn
  have IR2 : IntegrableOn (fun s => 4 / (b - a) ^ 3 * (s ^ 2 * reCorr h s)) (Ioc (0 : ℝ) (b - a)) :=
    (hR2.const_mul _).integrableOn
  have g1 : (∫ s in Ioc (0 : ℝ) (b - a), 3 / (b - a) * E) = 3 / (b - a) * ((b - a) * E) := by
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hw.le]
    ring
  have g2 : (∫ s in Ioc (0 : ℝ) (b - a), 4 * E / (b - a) ^ 3 * s ^ 2) =
      4 * E / (b - a) ^ 3 * ((b - a) ^ 3 / 3) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hw.le, integral_pow]
    norm_num
  have g3 : (∫ s in Ioc (0 : ℝ) (b - a), 3 / (b - a) * reCorr h s) =
      3 / (b - a) * (‖∫ x, h x‖ ^ 2 / 2) := by
    rw [integral_const_mul, setIntegral_Ioc_reCorr h hc a b hab.le hs]
  have g4 : (∫ s in Ioc (0 : ℝ) (b - a), 4 / (b - a) ^ 3 * (s ^ 2 * reCorr h s)) =
      4 / (b - a) ^ 3 * qMom h a := by
    rw [integral_const_mul, setIntegral_Ioc_sq_reCorr h hc a b hab.le hs a]
  rw [hexp, integral_sub Ipoly Icorr, integral_sub Iconst Isq, integral_sub IR1 IR2, g1, g2, g3, g4]
  field_simp
  ring

/-- **Quadratic gain**, Bochner form. -/
theorem quad_gain (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ) (hab : a < b)
    (hs : ∀ x, x ∉ Ioo a b → h x = 0)
    (hint : IntegrableOn (fun s => ((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s)
      (Ioc (0 : ℝ) (b - a))) :
    (Real.log 2 + 4 / 3) * (∫ x, ‖h x‖ ^ 2) - 3 * ‖∫ x, h x‖ ^ 2 / (2 * (b - a)) +
        4 * qMom h a / (b - a) ^ 3 ≤
      ∫ s in Ioc (0 : ℝ) (b - a), ((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s := by
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
  have hR2 := integrable_sq_reCorr h hc a b hs'
  have hdiff : ∀ s, 0 ≤ E - reCorr h s := by
    intro s
    have hA := sq_norm_sub_shift h hc a b hs' s
    have h0 : 0 ≤ ∫ x, ‖h (x + s) - h x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    unfold reCorr
    linarith
  have Ip : IntegrableOn (fun s => (3 / (b - a) - 4 * s ^ 2 / (b - a) ^ 3) * (E - reCorr h s))
      (Ioc (0 : ℝ) (b - a)) := by
    have e : (fun s => (3 / (b - a) - 4 * s ^ 2 / (b - a) ^ 3) * (E - reCorr h s)) =
        fun s => (3 / (b - a) * E - 4 * E / (b - a) ^ 3 * s ^ 2) -
          (3 / (b - a) * reCorr h s - 4 / (b - a) ^ 3 * (s ^ 2 * reCorr h s)) := by
      funext s
      ring
    rw [e]
    exact ((continuous_const.sub (continuous_const.mul (continuous_id.pow 2))).integrableOn_Ioc).sub
      ((hR.const_mul _).sub (hR2.const_mul _)).integrableOn
  have hφeq : ∀ s ∈ Ioc (0 : ℝ) (b - a),
      (E - (∫ x, h (x + s) * conj (h x)).re) / s =
        (3 / (b - a) - 4 * s ^ 2 / (b - a) ^ 3) * (E - reCorr h s) + wt2 (b - a) s * (E - reCorr h s) := by
    intro s hs01
    have hs0 : s ≠ 0 := hs01.1.ne'
    unfold wt2 reCorr
    field_simp
    ring
  have Iw : IntegrableOn (fun s => wt2 (b - a) s * (E - reCorr h s)) (Ioc (0 : ℝ) (b - a)) := by
    have e : ∀ s ∈ Ioc (0 : ℝ) (b - a), wt2 (b - a) s * (E - reCorr h s) =
        (E - (∫ x, h (x + s) * conj (h x)).re) / s -
          (3 / (b - a) - 4 * s ^ 2 / (b - a) ^ 3) * (E - reCorr h s) := by
      intro s hs01
      rw [hφeq s hs01]
      ring
    exact (hint.sub Ip).congr_fun (fun s hs01 => (e s hs01).symm) measurableSet_Ioc
  rw [setIntegral_congr_fun measurableSet_Ioc hφeq, integral_add Ip Iw, setIntegral_Ioc_p_part h hc a b hab hs']
  -- weighted columns
  have hcol : (Real.log 2 - 1 / 3) * E ≤ ∫ s in Ioc (0 : ℝ) (b - a), wt2 (b - a) s * (E - reCorr h s) := by
    have hnn : ∀ s ∈ Ioc (0 : ℝ) (b - a), 0 ≤ wt2 (b - a) s * (E - reCorr h s) :=
      fun s hs01 => mul_nonneg (wt2_nonneg _ _ hs01.1 hw) (hdiff s)
    have hΦm : Measurable (Function.uncurry fun (s x : ℝ) => ENNReal.ofReal (wt2 (b - a) s) *
        ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0))) := by
      change Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (wt2 (b - a) p.1) *
        ((if b - p.1 < p.2 then sqG h p.2 else 0) + (if p.2 < a + p.1 then sqG h p.2 else 0)))
      have hwm : Measurable (fun p : ℝ × ℝ => wt2 (b - a) p.1) := by
        unfold wt2
        exact (measurable_fst.inv.sub_const _).add
          ((measurable_const.mul (measurable_fst.pow_const 2)).div_const _)
      refine (hwm.ennreal_ofReal).mul (Measurable.add ?_ ?_)
      · exact Measurable.ite (measurableSet_lt (measurable_const.sub measurable_fst) measurable_snd)
          (hGm.comp measurable_snd) measurable_const
      · exact Measurable.ite (measurableSet_lt measurable_snd (measurable_const.add measurable_fst))
          (hGm.comp measurable_snd) measurable_const
    have hswap := lintegral_lintegral_swap (μ := volume.restrict (Ioc (0 : ℝ) (b - a)))
      (ν := (volume : Measure ℝ)) hΦm.aemeasurable
    have hupper : ∀ s ∈ Ioc (0 : ℝ) (b - a),
        ∫⁻ x, ENNReal.ofReal (wt2 (b - a) s) *
            ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) ≤
          2 * ENNReal.ofReal (wt2 (b - a) s * (E - reCorr h s)) := by
      intro s hs01
      have hwt := wt2_nonneg (b - a) s hs01.1 hw
      have hm1 : Measurable (fun x : ℝ => if b - s < x then sqG h x else 0) :=
        Measurable.ite (measurableSet_lt measurable_const measurable_id) hGm measurable_const
      have hm2 : Measurable (fun x : ℝ => if x < a + s then sqG h x else 0) :=
        Measurable.ite (measurableSet_lt measurable_id measurable_const) hGm measurable_const
      have hm12 : Measurable (fun x : ℝ =>
          (if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) := hm1.add hm2
      rw [lintegral_const_mul _ hm12]
      calc ENNReal.ofReal (wt2 (b - a) s) *
            ∫⁻ x, ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0))
          ≤ ENNReal.ofReal (wt2 (b - a) s) * ENNReal.ofReal (2 * (E - reCorr h s)) :=
            mul_le_mul_right (row_key h hc a b hs s hs01.1 hs01.2) _
        _ = 2 * ENNReal.ofReal (wt2 (b - a) s * (E - reCorr h s)) := by
            rw [← ENNReal.ofReal_mul hwt, ← ENNReal.ofReal_ofNat 2,
              ← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            ring
    have hlog : (1 / 3 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal ((Real.log 2 - 1 / 3) * E) ≤
        2 * ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal (wt2 (b - a) s * (E - reCorr h s)) := by
      calc (2 : ℝ≥0∞) * ENNReal.ofReal ((Real.log 2 - 1 / 3) * E)
          = ∫⁻ x, sqG h x * ENNReal.ofReal (2 * Real.log 2 - 2 / 3) := by
            rw [lintegral_mul_const _ hGm, ← hEl, ← ENNReal.ofReal_mul hE0, ← ENNReal.ofReal_ofNat 2,
              ← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            ring
        _ ≤ ∫⁻ x, ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal (wt2 (b - a) s) *
              ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) :=
            lintegral_mono (fun x => column_wt2 h a b hab hs x)
        _ = ∫⁻ s in Ioc (0 : ℝ) (b - a), ∫⁻ x, ENNReal.ofReal (wt2 (b - a) s) *
              ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) := hswap.symm
        _ ≤ ∫⁻ s in Ioc (0 : ℝ) (b - a), 2 * ENNReal.ofReal (wt2 (b - a) s * (E - reCorr h s)) :=
            setLIntegral_mono' measurableSet_Ioc hupper
        _ = 2 * ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal (wt2 (b - a) s * (E - reCorr h s)) :=
            lintegral_const_mul' _ _ (by simp)
    have h3 := (ENNReal.mul_le_mul_iff_right (by norm_num) (by simp)).mp h2
    rw [← ofReal_integral_eq_lintegral_ofReal Iw
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs01; exact hnn s hs01)] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (setIntegral_nonneg measurableSet_Ioc hnn)).mp h3
  linarith

end AEGIS.WeilDiagonalQuadGainV1

#print axioms AEGIS.WeilDiagonalQuadGainV1.integral_sq_autocorr
#print axioms AEGIS.WeilDiagonalQuadGainV1.column_wt2
#print axioms AEGIS.WeilDiagonalQuadGainV1.quad_gain
