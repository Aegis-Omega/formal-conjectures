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

import Mathlib

/-!
AEGIS Ω — the diagonal log-gain sub-lemma S1 (Claude Lab, 2026-11-21).

For `h : ℝ → ℂ` continuous and vanishing outside `[a, b]`, with `E = ∫ ‖h‖²` and
`C(s) = ∫ h (x + s) · conj (h x) dx`,

  `log 2 · E ≤ ∫_{(0, b − a]} (E − Re C(s)) / s ds`

(`log_gain_lintegral` as a lower Lebesgue integral; `log_gain_interval` and, on `[0, 1]`, `log_gain` as Bochner
integrals when the right side is integrable). This is S1 of `research/rh/atomic_map_v1` (AEGIS-OMEGA PR #835,
§4.3), stated on a general interval so that it applies to a packet of log-width `w = b − a` without rescaling.
The proof follows the four steps given there:
1. `E − Re C(s) = ½ ∫ ‖h(x+s) − h(x)‖²`;
2. for `0 < s ≤ b − a` the integrand is at least `‖h x‖²·[x > b − s] + ‖h(x+s)‖²·[x < a]`;
3. Tonelli turns the `1/s` integral of these into the weights `log (w/(b−x))` and `log (w/(x−a))`;
4. `log (w/(b−x)) + log (w/(x−a)) ≥ 2 log 2` on `(a, b)`, because `4 (b−x)(x−a) ≤ w²`.

Abstract real analysis only. It is the first step of a diagonal lower bound for the Weil form; it is not a
statement about zeta and not RH.
-/

open MeasureTheory Set
open scoped ComplexConjugate ENNReal
set_option autoImplicit false
noncomputable section
namespace AEGIS.WeilDiagonalLogGainS1V1

theorem integrable_of_zero_off {F : Type*} [NormedAddCommGroup F] (f : ℝ → F) (hf : Continuous f)
    (a b : ℝ) (h0 : ∀ x, x ∉ Icc a b → f x = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun x hx => by
      by_contra hn
      exact hx (h0 x hn)))

/-- A continuous function vanishing outside `[a, b]` vanishes at `a` and `b`. -/
theorem zero_off_Ioo_of_continuous (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) : ∀ x, x ∉ Ioo a b → h x = 0 := by
  have hcl : IsClosed {x : ℝ | h x = 0} := isClosed_eq hc continuous_const
  intro x hx
  by_cases hx' : x ∈ Icc a b
  · obtain ⟨h0, h1⟩ := hx'
    rcases eq_or_lt_of_le h0 with e0 | l0
    · have hsub : Iio a ⊆ {y : ℝ | h y = 0} :=
        fun y hy => hs y (fun hm => absurd hm.1 (not_le.mpr hy))
      have hcl' := hcl.closure_subset_iff.mpr hsub
      rw [closure_Iio] at hcl'
      have ha : h a = 0 := hcl' (le_refl a)
      rw [← e0]
      exact ha
    · rcases eq_or_lt_of_le h1 with e1 | l1
      · have hsub : Ioi b ⊆ {y : ℝ | h y = 0} :=
          fun y hy => hs y (fun hm => absurd hm.2 (not_le.mpr hy))
        have hcl' := hcl.closure_subset_iff.mpr hsub
        rw [closure_Ioi] at hcl'
        have hb : h b = 0 := hcl' (le_refl b)
        rw [e1]
        exact hb
      · exact absurd ⟨l0, l1⟩ hx
  · exact hs x hx'

/-- Step 1: `∫ ‖h(x+s) − h x‖² = 2 (E − Re C(s))`. -/
theorem sq_norm_sub_shift (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Icc a b → h x = 0) (s : ℝ) :
    (∫ x, ‖h (x + s) - h x‖ ^ 2) =
      2 * ((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) := by
  have hsh : Continuous (fun x => h (x + s)) := hc.comp (continuous_add_const s)
  have hz1 : ∀ x, x ∉ Icc (a - s) (b - s) → h (x + s) = 0 := fun x hx =>
    hs _ (fun hm => hx ⟨by linarith [hm.1], by linarith [hm.2]⟩)
  have I1 : Integrable (fun x => ‖h (x + s)‖ ^ 2) :=
    integrable_of_zero_off _ (hsh.norm.pow 2) (a - s) (b - s) (fun x hx => by simp [hz1 x hx])
  have I2 : Integrable (fun x => ‖h x‖ ^ 2) :=
    integrable_of_zero_off _ (hc.norm.pow 2) a b (fun x hx => by simp [hs x hx])
  have I4 : Integrable (fun x => h (x + s) * conj (h x)) :=
    integrable_of_zero_off _ (hsh.mul (Complex.continuous_conj.comp hc)) a b
      (fun x hx => by simp [hs x hx])
  have I3 : Integrable (fun x => 2 * (h (x + s) * conj (h x)).re) :=
    integrable_of_zero_off _
      (continuous_const.mul (Complex.continuous_re.comp (hsh.mul (Complex.continuous_conj.comp hc))))
      a b (fun x hx => by simp [hs x hx])
  have hpt : (fun x => ‖h (x + s) - h x‖ ^ 2) =
      fun x => ‖h (x + s)‖ ^ 2 + ‖h x‖ ^ 2 - 2 * (h (x + s) * conj (h x)).re := by
    funext x
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub]
  have e1 : (∫ x, (‖h (x + s)‖ ^ 2 + ‖h x‖ ^ 2 - 2 * (h (x + s) * conj (h x)).re)) =
      (∫ x, (‖h (x + s)‖ ^ 2 + ‖h x‖ ^ 2)) - ∫ x, 2 * (h (x + s) * conj (h x)).re :=
    integral_sub (I1.add I2) I3
  have e2 : (∫ x, (‖h (x + s)‖ ^ 2 + ‖h x‖ ^ 2)) = (∫ x, ‖h (x + s)‖ ^ 2) + ∫ x, ‖h x‖ ^ 2 :=
    integral_add I1 I2
  have e3 : (∫ x, 2 * (h (x + s) * conj (h x)).re) = 2 * ∫ x, (h (x + s) * conj (h x)).re :=
    integral_const_mul 2 _
  have e4 : (∫ x, ‖h (x + s)‖ ^ 2) = ∫ x, ‖h x‖ ^ 2 :=
    integral_add_right_eq_self (fun x => ‖h x‖ ^ 2) s
  have hre : (∫ x, (h (x + s) * conj (h x)).re) = (∫ x, h (x + s) * conj (h x)).re := by
    have h' := Complex.reCLM.integral_comp_comm I4
    simpa using h'
  rw [hpt, e1, e2, e3, e4, hre]
  ring

/-- `‖h x‖²` as an extended nonnegative real. -/
def sqG (h : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (‖h x‖ ^ 2)

theorem sqG_measurable (h : ℝ → ℂ) (hc : Continuous h) : Measurable (sqG h) :=
  (hc.norm.pow 2).measurable.ennreal_ofReal

/-- Step 2: the pointwise lower bound, `s ≤ b − a`. -/
theorem pointwise_lower (h : ℝ → ℂ) (a b : ℝ) (hs : ∀ x, x ∉ Ioo a b → h x = 0)
    (s : ℝ) (hs1 : s ≤ b - a) (x : ℝ) :
    (if b - s < x then sqG h x else 0) + (if x < a then sqG h (x + s) else 0) ≤
      ENNReal.ofReal (‖h (x + s) - h x‖ ^ 2) := by
  by_cases c1 : b - s < x
  · have c2 : ¬ x < a := fun h' => by linarith
    have hz : h (x + s) = 0 := hs _ (fun hm => by linarith [hm.2])
    rw [if_pos c1, if_neg c2, add_zero]
    simp [sqG, hz]
  · by_cases c2 : x < a
    · have hz : h x = 0 := hs _ (fun hm => by linarith [hm.1])
      rw [if_neg c1, if_pos c2, zero_add]
      simp [sqG, hz]
    · rw [if_neg c1, if_neg c2, add_zero]
      simp

/-- The row of the double integral at a fixed `s ∈ (0, b − a]`. -/
theorem row_bound (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ) (hs : ∀ x, x ∉ Ioo a b → h x = 0)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ b - a) :
    ENNReal.ofReal s⁻¹ *
        ∫⁻ x, ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) ≤
      2 * ENNReal.ofReal (((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s) := by
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
  have key : ∫⁻ x, ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) ≤
      ENNReal.ofReal (2 * ((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re)) := by
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
  calc ENNReal.ofReal s⁻¹ *
        ∫⁻ x, ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0))
      ≤ ENNReal.ofReal s⁻¹ *
          ENNReal.ofReal (2 * ((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re)) :=
        mul_le_mul_right key _
    _ = 2 * ENNReal.ofReal (((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hs0.le), ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- `∫_{(c,d]} ds/s = log (d/c)` as a lower Lebesgue integral. -/
theorem lintegral_inv_Ioc (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d) :
    ∫⁻ s in Ioc c d, ENNReal.ofReal s⁻¹ = ENNReal.ofReal (Real.log (d / c)) := by
  have hint : IntegrableOn (fun s : ℝ => s⁻¹) (Ioc c d) := by
    have hco : ContinuousOn (fun s : ℝ => s⁻¹) (Icc c d) :=
      continuousOn_inv₀.mono (fun s hs => (lt_of_lt_of_le hc hs.1).ne')
    exact (hco.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← intervalIntegral.integral_of_le hcd, integral_inv_of_pos hc (lt_of_lt_of_le hc hcd)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact inv_nonneg.mpr (lt_trans hc hs.1).le

theorem lintegral_Ioc_indicator_Ioi (c w : ℝ) (hc : 0 ≤ c) (f : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioc (0 : ℝ) w, (Ioi c).indicator f s = ∫⁻ s in Ioc c w, f s := by
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi c ∩ Ioc (0 : ℝ) w = Ioc c w := by
    ext s
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, lt_of_le_of_lt hc h1, h3⟩
  rw [hset]

/-- Step 4: `2 log 2 ≤ log ((b−a)/(b−x)) + log ((b−a)/(x−a))` on `(a, b)`. -/
theorem two_log_two_le (a b x : ℝ) (hx0 : a < x) (hx1 : x < b) :
    2 * Real.log 2 ≤ Real.log ((b - a) / (b - x)) + Real.log ((b - a) / (x - a)) := by
  have p1 : 0 < b - x := by linarith
  have p2 : 0 < x - a := by linarith
  have pw : 0 < b - a := by linarith
  rw [← Real.log_mul (div_pos pw p1).ne' (div_pos pw p2).ne']
  have h4 : (4 : ℝ) ≤ (b - a) / (b - x) * ((b - a) / (x - a)) := by
    rw [div_mul_div_comm, le_div_iff₀ (mul_pos p1 p2)]
    nlinarith [sq_nonneg (b + a - 2 * x)]
  have hl := Real.log_le_log (by norm_num) h4
  have e4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  linarith

/-- The column of the double integral at a fixed `x`. -/
theorem column_bound (h : ℝ → ℂ) (a b : ℝ) (hs : ∀ x, x ∉ Ioo a b → h x = 0) (x : ℝ) :
    sqG h x * ENNReal.ofReal (2 * Real.log 2) ≤
      ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal s⁻¹ *
        ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) := by
  by_cases hx : x ∈ Ioo a b
  · obtain ⟨hx0, hx1⟩ := hx
    have hfun : (fun s : ℝ => ENNReal.ofReal s⁻¹ *
        ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0))) =
        fun s => sqG h x * ((Ioi (b - x)).indicator (fun s : ℝ => ENNReal.ofReal s⁻¹) s +
          (Ioi (x - a)).indicator (fun s : ℝ => ENNReal.ofReal s⁻¹) s) := by
      funext s
      have e1 : (b - s < x) ↔ (b - x < s) := ⟨fun h' => by linarith, fun h' => by linarith⟩
      have e2 : (x < a + s) ↔ (x - a < s) := ⟨fun h' => by linarith, fun h' => by linarith⟩
      simp only [Set.indicator_apply, mem_Ioi]
      by_cases c1 : b - x < s <;> by_cases c2 : x - a < s <;>
        simp only [e1, e2, c1, c2, if_true, if_false, add_zero, zero_add,
          mul_zero] <;>
        ring
    have hm : Measurable (fun s : ℝ => ENNReal.ofReal s⁻¹) := measurable_inv.ennreal_ofReal
    have hmsum : Measurable (fun s : ℝ => (Ioi (b - x)).indicator (fun s : ℝ => ENNReal.ofReal s⁻¹) s +
        (Ioi (x - a)).indicator (fun s : ℝ => ENNReal.ofReal s⁻¹) s) :=
      (hm.indicator measurableSet_Ioi).add (hm.indicator measurableSet_Ioi)
    rw [hfun, lintegral_const_mul _ hmsum,
      lintegral_add_left (hm.indicator measurableSet_Ioi),
      lintegral_Ioc_indicator_Ioi (b - x) (b - a) (by linarith) _,
      lintegral_Ioc_indicator_Ioi (x - a) (b - a) (by linarith) _,
      lintegral_inv_Ioc (b - x) (b - a) (by linarith) (by linarith),
      lintegral_inv_Ioc (x - a) (b - a) (by linarith) (by linarith)]
    have n1 : 0 ≤ Real.log ((b - a) / (b - x)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    have n2 : 0 ≤ Real.log ((b - a) / (x - a)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
    rw [← ENNReal.ofReal_add n1 n2]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (two_log_two_le a b x hx0 hx1)) _
  · simp [sqG, hs x hx]

/-- **S1, lower Lebesgue integral form**, on a general interval `[a, b]`. -/
theorem log_gain_lintegral (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Ioo a b → h x = 0) :
    ENNReal.ofReal (Real.log 2 * ∫ x, ‖h x‖ ^ 2) ≤
      ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal
        (((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s) := by
  have hs' : ∀ x, x ∉ Icc a b → h x = 0 := fun x hx => hs x (fun h' => hx (Ioo_subset_Icc_self h'))
  have hGm := sqG_measurable h hc
  have hint2 : Integrable (fun x => ‖h x‖ ^ 2) :=
    integrable_of_zero_off _ (hc.norm.pow 2) a b (fun x hx => by simp [hs' x hx])
  have hE : ENNReal.ofReal (∫ x, ‖h x‖ ^ 2) = ∫⁻ x, sqG h x :=
    ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall (fun x => sq_nonneg ‖h x‖))
  have hE0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  have hΦm : Measurable (Function.uncurry fun (s x : ℝ) => ENNReal.ofReal s⁻¹ *
      ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0))) := by
    change Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1⁻¹ *
      ((if b - p.1 < p.2 then sqG h p.2 else 0) + (if p.2 < a + p.1 then sqG h p.2 else 0)))
    refine (measurable_fst.inv.ennreal_ofReal).mul (Measurable.add ?_ ?_)
    · exact Measurable.ite (measurableSet_lt (measurable_const.sub measurable_fst) measurable_snd)
        (hGm.comp measurable_snd) measurable_const
    · exact Measurable.ite (measurableSet_lt measurable_snd (measurable_const.add measurable_fst))
        (hGm.comp measurable_snd) measurable_const
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Ioc (0 : ℝ) (b - a)))
    (ν := (volume : Measure ℝ)) hΦm.aemeasurable
  have hupper : ∀ s ∈ Ioc (0 : ℝ) (b - a),
      ∫⁻ x, ENNReal.ofReal s⁻¹ *
          ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) ≤
        2 * ENNReal.ofReal (((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s) := by
    intro s hs01
    have hm1 : Measurable (fun x : ℝ => if b - s < x then sqG h x else 0) :=
      Measurable.ite (measurableSet_lt measurable_const measurable_id) hGm measurable_const
    have hm2 : Measurable (fun x : ℝ => if x < a + s then sqG h x else 0) :=
      Measurable.ite (measurableSet_lt measurable_id measurable_const) hGm measurable_const
    have hm12 : Measurable (fun x : ℝ =>
        (if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) := hm1.add hm2
    rw [lintegral_const_mul _ hm12]
    exact row_bound h hc a b hs s hs01.1 hs01.2
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (Real.log 2 * ∫ x, ‖h x‖ ^ 2) ≤
      2 * ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal
        (((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s) := by
    calc (2 : ℝ≥0∞) * ENNReal.ofReal (Real.log 2 * ∫ x, ‖h x‖ ^ 2)
        = ∫⁻ x, sqG h x * ENNReal.ofReal (2 * Real.log 2) := by
          rw [lintegral_mul_const _ hGm, ← hE, ← ENNReal.ofReal_mul hE0, ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
      _ ≤ ∫⁻ x, ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal s⁻¹ *
            ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) :=
          lintegral_mono (fun x => column_bound h a b hs x)
      _ = ∫⁻ s in Ioc (0 : ℝ) (b - a), ∫⁻ x, ENNReal.ofReal s⁻¹ *
            ((if b - s < x then sqG h x else 0) + (if x < a + s then sqG h x else 0)) := hswap.symm
      _ ≤ ∫⁻ s in Ioc (0 : ℝ) (b - a), 2 * ENNReal.ofReal
            (((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s) :=
          setLIntegral_mono' measurableSet_Ioc hupper
      _ = 2 * ∫⁻ s in Ioc (0 : ℝ) (b - a), ENNReal.ofReal
            (((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s) :=
          lintegral_const_mul' _ _ (by simp)
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by simp)).mp h2

/-- **S1** on `[a, b]`, Bochner form, when the right-hand side is integrable. -/
theorem log_gain_interval (h : ℝ → ℂ) (hc : Continuous h) (a b : ℝ)
    (hs : ∀ x, x ∉ Icc a b → h x = 0)
    (hint : IntegrableOn (fun s : ℝ => ((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s)
      (Ioc 0 (b - a))) :
    Real.log 2 * (∫ x, ‖h x‖ ^ 2) ≤
      ∫ s in Ioc (0 : ℝ) (b - a), ((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s := by
  have hs0 := zero_off_Ioo_of_continuous h hc a b hs
  have hnn : ∀ s ∈ Ioc (0 : ℝ) (b - a),
      0 ≤ ((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s := by
    intro s hs01
    have hA := sq_norm_sub_shift h hc a b hs s
    have h0 : 0 ≤ ∫ x, ‖h (x + s) - h x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    exact div_nonneg (by linarith) hs01.1.le
  have hl := log_gain_lintegral h hc a b hs0
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hnn))] at hl
  exact (ENNReal.ofReal_le_ofReal_iff (setIntegral_nonneg measurableSet_Ioc hnn)).mp hl

/-- **S1** as stated in PR #835 §4.5: `h` continuous, vanishing outside `[0, 1]`. -/
theorem log_gain (h : ℝ → ℂ) (hc : Continuous h) (hs : ∀ x, x ∉ Icc (0 : ℝ) 1 → h x = 0)
    (hint : IntegrableOn (fun s : ℝ => ((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s)
      (Ioc 0 1)) :
    Real.log 2 * (∫ x, ‖h x‖ ^ 2) ≤
      ∫ s in Ioc (0 : ℝ) 1, ((∫ x, ‖h x‖ ^ 2) - (∫ x, h (x + s) * conj (h x)).re) / s := by
  have e : (1 : ℝ) - 0 = 1 := by norm_num
  have hg := log_gain_interval h hc 0 1 hs (by rw [e]; exact hint)
  rwa [e] at hg

end AEGIS.WeilDiagonalLogGainS1V1

#print axioms AEGIS.WeilDiagonalLogGainS1V1.sq_norm_sub_shift
#print axioms AEGIS.WeilDiagonalLogGainS1V1.log_gain_lintegral
#print axioms AEGIS.WeilDiagonalLogGainS1V1.log_gain_interval
#print axioms AEGIS.WeilDiagonalLogGainS1V1.log_gain
