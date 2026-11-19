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

import WeilCriterionCompactSmoothV1
import WeilLogChangeOfVariablesV1
import WeilMomentKillerRangeV1

/-!
# Every multiplicative moment-zero Weil packet is a moment-killer image, V1

`WeilLogChangeOfVariablesV1` transports a log-coordinate moment-killer image `momentKiller ψ` to a
multiplicative packet `mulPacket (momentKiller ψ)` satisfying `WeilMomentConditionsV1`. This file
proves the converse for the canonical domain `WeilCompactSmoothGV1`:

* `exists_momentKiller_packet`: if `g` satisfies `WeilMomentConditionsV1` and vanishes for
  `x ≤ e^a` and for `x ≥ e^b`, then
  `g x = mulPacket (momentKiller ψr) x + mulPacket (momentKiller ψi) x * I` for all `x`, with `ψr`,
  `ψi` smooth and vanishing outside `[a, b]`, the same log window as `g`.

The real and imaginary parts `u ↦ Re g(e^u)`, `u ↦ Im g(e^u)` inherit both log-coordinate moments from
the two multiplicative ones (`integral_inv_mul_comp_log`, `integral_comp_log`), and
`WeilMomentKillerRangeV1.exists_momentKiller_eq_of_vanish` gives their potentials.
-/

open MeasureTheory Set Complex
open scoped ContDiff

noncomputable section

namespace AEGIS.WeilMomentKillerPacketRangeV1

open AEGIS.WeilMomentKillerConstructionV1 AEGIS.WeilMomentKillerRangeV1

/-- A canonical moment-zero packet with log window `[a, b]` is a moment-killer image, componentwise. -/
theorem exists_momentKiller_packet (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    {a b : ℝ} (hab : a ≤ b) (hl : ∀ x, x ≤ Real.exp a → g.1 x = 0)
    (hr : ∀ x, Real.exp b ≤ x → g.1 x = 0) :
    ∃ ψr ψi : ℝ → ℝ, ContDiff ℝ ∞ ψr ∧ ContDiff ℝ ∞ ψi ∧
      (∀ t, t ≤ a → ψr t = 0) ∧ (∀ t, b ≤ t → ψr t = 0) ∧
      (∀ t, t ≤ a → ψi t = 0) ∧ (∀ t, b ≤ t → ψi t = 0) ∧
      ∀ x, g.1 x = (AEGIS.WeilLogChangeOfVariablesV1.mulPacket (momentKiller ψr) x : ℂ) +
        (AEGIS.WeilLogChangeOfVariablesV1.mulPacket (momentKiller ψi) x : ℂ) * I := by
  obtain ⟨hgs, hgc, hgpos⟩ := g.2
  set φr : ℝ → ℝ := fun u => (g.1 (Real.exp u)).re with hφr
  set φi : ℝ → ℝ := fun u => (g.1 (Real.exp u)).im with hφi
  have hcomp : ContDiff ℝ ∞ fun u => g.1 (Real.exp u) := hgs.comp Real.contDiff_exp
  have hφrs : ContDiff ℝ ∞ φr := reCLM.contDiff.comp hcomp
  have hφis : ContDiff ℝ ∞ φi := imCLM.contDiff.comp hcomp
  have hgl : ∀ u, u ≤ a → g.1 (Real.exp u) = 0 := fun u hu => hl _ (Real.exp_le_exp.2 hu)
  have hgr : ∀ u, b ≤ u → g.1 (Real.exp u) = 0 := fun u hu => hr _ (Real.exp_le_exp.2 hu)
  have hrl : ∀ u, u ≤ a → φr u = 0 := fun u hu => by simp [hφr, hgl u hu]
  have hrr : ∀ u, b ≤ u → φr u = 0 := fun u hu => by simp [hφr, hgr u hu]
  have hil : ∀ u, u ≤ a → φi u = 0 := fun u hu => by simp [hφi, hgl u hu]
  have hir : ∀ u, b ≤ u → φi u = 0 := fun u hu => by simp [hφi, hgr u hu]
  have hlog : ∀ x, 0 < x → g.1 (Real.exp (Real.log x)) = g.1 x := fun x hx => by
    rw [Real.exp_log hx]
  -- integrability of `g x / x`: below `e^a` the packet vanishes, so `x` may be replaced by
  -- `max x (e^a)`, which keeps the quotient continuous
  set c := Real.exp a with hc_def
  have hc : 0 < c := Real.exp_pos a
  have hdiv : (fun x : ℝ => g.1 x / (x : ℂ)) = fun x => g.1 x * (((max x c : ℝ) : ℂ))⁻¹ := by
    funext x
    rcases le_or_gt x c with h | h
    · simp [hl x h]
    · rw [max_eq_left h.le, div_eq_mul_inv]
  have hint1 : Integrable fun x : ℝ => g.1 x / (x : ℂ) := by
    rw [hdiv]
    refine Continuous.integrable_of_hasCompactSupport ?_ (hgc.mul_right)
    refine hgs.continuous.mul (Continuous.inv₀ ?_ fun x => ?_)
    · exact continuous_ofReal.comp (continuous_id.max continuous_const)
    · exact_mod_cast (lt_of_lt_of_le hc (le_max_right x c)).ne'
  have hint0 : Integrable g.1 := hgs.continuous.integrable_of_hasCompactSupport hgc
  -- the two log-coordinate moments of a component `f = Re` or `Im`
  have hmom1 : (∫ x in Ioi (0 : ℝ), (g.1 x / (x : ℂ)).re) = 0 ∧
      (∫ x in Ioi (0 : ℝ), (g.1 x / (x : ℂ)).im) = 0 := by
    have h1 := integral_re (μ := volume.restrict (Ioi (0 : ℝ))) hint1.integrableOn
    have h2 := integral_im (μ := volume.restrict (Ioi (0 : ℝ))) hint1.integrableOn
    simp only [RCLike.re_to_complex, RCLike.im_to_complex] at h1 h2
    exact ⟨by rw [h1, hm.1]; simp, by rw [h2, hm.1]; simp⟩
  have hmom2 : (∫ x in Ioi (0 : ℝ), (g.1 x).re) = 0 ∧ (∫ x in Ioi (0 : ℝ), (g.1 x).im) = 0 := by
    have h1 := integral_re (μ := volume.restrict (Ioi (0 : ℝ))) hint0.integrableOn
    have h2 := integral_im (μ := volume.restrict (Ioi (0 : ℝ))) hint0.integrableOn
    simp only [RCLike.re_to_complex, RCLike.im_to_complex] at h1 h2
    exact ⟨by rw [h1, hm.2]; simp, by rw [h2, hm.2]; simp⟩
  have hr1 : ∫ u, φr u = 0 := by
    rw [← AEGIS.WeilLogChangeOfVariablesV1.integral_inv_mul_comp_log hφrs.continuous hrl hrr]
    calc ∫ x in Ioi (0 : ℝ), x⁻¹ * φr (Real.log x)
        = ∫ x in Ioi (0 : ℝ), (g.1 x / (x : ℂ)).re :=
          setIntegral_congr_fun measurableSet_Ioi fun x hx => by
            simp only [hφr, hlog x hx, div_ofReal_re]
            ring
      _ = 0 := hmom1.1
  have hi1 : ∫ u, φi u = 0 := by
    rw [← AEGIS.WeilLogChangeOfVariablesV1.integral_inv_mul_comp_log hφis.continuous hil hir]
    calc ∫ x in Ioi (0 : ℝ), x⁻¹ * φi (Real.log x)
        = ∫ x in Ioi (0 : ℝ), (g.1 x / (x : ℂ)).im :=
          setIntegral_congr_fun measurableSet_Ioi fun x hx => by
            simp only [hφi, hlog x hx, div_ofReal_im]
            ring
      _ = 0 := hmom1.2
  have hr2 : ∫ u, φr u * Real.exp u = 0 := by
    rw [← AEGIS.WeilLogChangeOfVariablesV1.integral_comp_log hφrs.continuous hrl hrr]
    calc ∫ x in Ioi (0 : ℝ), φr (Real.log x) = ∫ x in Ioi (0 : ℝ), (g.1 x).re :=
          setIntegral_congr_fun measurableSet_Ioi fun x hx => by simp only [hφr, hlog x hx]
      _ = 0 := hmom2.1
  have hi2 : ∫ u, φi u * Real.exp u = 0 := by
    rw [← AEGIS.WeilLogChangeOfVariablesV1.integral_comp_log hφis.continuous hil hir]
    calc ∫ x in Ioi (0 : ℝ), φi (Real.log x) = ∫ x in Ioi (0 : ℝ), (g.1 x).im :=
          setIntegral_congr_fun measurableSet_Ioi fun x hx => by simp only [hφi, hlog x hx]
      _ = 0 := hmom2.2
  obtain ⟨ψr, hψrs, hψrl, hψrr, hψr⟩ := exists_momentKiller_eq_of_vanish hab hφrs hrl hrr hr1 hr2
  obtain ⟨ψi, hψis, hψil, hψir, hψi⟩ := exists_momentKiller_eq_of_vanish hab hφis hil hir hi1 hi2
  refine ⟨ψr, ψi, hψrs, hψis, hψrl, hψrr, hψil, hψir, fun x => ?_⟩
  rw [hψr, hψi]
  rcases le_or_gt x 0 with hx | hx
  · rw [AEGIS.WeilLogChangeOfVariablesV1.mulPacket_of_nonpos hx,
      AEGIS.WeilLogChangeOfVariablesV1.mulPacket_of_nonpos hx]
    simp only [ofReal_zero, zero_mul, add_zero]
    exact image_eq_zero_of_notMem_tsupport fun h => (not_lt.2 hx) (hgpos h)
  · rw [AEGIS.WeilLogChangeOfVariablesV1.mulPacket_of_pos hx,
      AEGIS.WeilLogChangeOfVariablesV1.mulPacket_of_pos hx]
    simp only [hφr, hφi, hlog x hx]
    exact (re_add_im (g.1 x)).symm

end AEGIS.WeilMomentKillerPacketRangeV1

#print axioms AEGIS.WeilMomentKillerPacketRangeV1.exists_momentKiller_packet
