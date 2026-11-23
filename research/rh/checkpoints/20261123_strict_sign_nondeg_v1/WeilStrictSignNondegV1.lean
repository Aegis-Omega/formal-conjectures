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

import WeilFineBudgetEquivV1
import WeilRHImpliesFinalSignV13

/-!
AEGIS Ω — the strict Weil sign is RH plus nondegeneracy of the Weil form (Claude Lab, 2026-11-23).

`WeilNondegenerate`: a moment-zero packet `g` with `Re B(g, h) = 0` for every moment-zero packet `h` is zero.

* `re_B_add_scale`: `Re B(g + t h, g + t h) = Re B(g, g) + 2 t Re B(g, h) + t² Re B(h, h)` for real `t`.
* `strictWeilSign_of_rh_nondeg`: under RH the form `−Re B` is positive semidefinite on moment-zero packets
  (`rh_implies_final_sign_residual_v13`); a packet with `Re B(g, g) = 0` is then a null vector, so
  `Re B(g, h) = 0` for every `h`, and nondegeneracy gives `g = 0`.
* `rh_and_nondeg_of_strictWeilSign`, `strictWeilSign_iff_rh_and_nondeg`.
* `fineBudget_iff_rh_and_nondeg`: for `c ≤ 43/10`, the per-packet fine budget is exactly RH together with
  `WeilNondegenerate`.

`WeilNondegenerate` is NOT proved here. Not RH.
-/

open Set Finset Complex
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilStrictSignNondegV1

open AEGIS.WeilMixedAlgebraV2 AEGIS.WeilFineBudgetEquivV1

/-- Nondegeneracy of the real Weil form on moment-zero packets. -/
def WeilNondegenerate : Prop :=
  ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
    (∀ h : WeilCompactSmoothGV1, WeilMomentConditionsV1 h → (B g h).re = 0) → g.1 = 0

theorem re_B_add_scale (g h : WeilCompactSmoothGV1) (t : ℝ) :
    (B (addPacket g (scalePacket (t : ℂ) h)) (addPacket g (scalePacket (t : ℂ) h))).re =
      (B g g).re + 2 * t * (B g h).re + t ^ 2 * (B h h).re := by
  simp only [B_add_left, B_add_right, B_scale_left, B_scale_right]
  have hs : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  rw [hs, B_hermitian g h]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.conj_re]
  ring

/-- RH and nondegeneracy give the strict Weil sign. -/
theorem strictWeilSign_of_rh_nondeg (hRH : RiemannHypothesis) (hN : WeilNondegenerate) :
    StrictWeilSign := by
  intro g hm hg0
  have hsign := AEGIS.WeilRHImpliesFinalSignV13.rh_implies_final_sign_residual_v13 hRH
  have hQ : ∀ f : WeilCompactSmoothGV1, WeilMomentConditionsV1 f → (B f f).re ≤ 0 :=
    fun f hf => hsign f hf
  change (B g g).re < 0
  rcases lt_or_eq_of_le (hQ g hm) with hlt | heq
  · exact hlt
  · exfalso
    apply hg0
    apply hN g hm
    intro h hh
    have hq : ∀ t : ℝ, 2 * t * (B g h).re + t ^ 2 * (B h h).re ≤ 0 := by
      intro t
      have ht := hQ (addPacket g (scalePacket (t : ℂ) h))
        (AEGIS.RestrictedWeilCriterionKernelBridgeV10.addPacket_preserves_moments_v10 g
          (scalePacket (t : ℂ) h) hm
          (AEGIS.RestrictedWeilCriterionKernelBridgeV10.scalePacket_preserves_moments_v10 (t : ℂ) h hh))
      rw [re_B_add_scale, heq] at ht
      linarith
    have hy : (B h h).re ≤ 0 := hQ h hh
    by_contra hx
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = 1 / (1 - (B h h).re) := ⟨_, rfl⟩
    have hpos1 : 0 < 1 - (B h h).re := by linarith
    have hs0 : 0 < s := by rw [hsdef]; exact one_div_pos.mpr hpos1
    have hs1 : s * (1 - (B h h).re) = 1 := by rw [hsdef, one_div, inv_mul_cancel₀ hpos1.ne']
    have e2 : s * (1 - (B h h).re) = s - s * (B h h).re := by ring
    have hsy : 0 < 2 + s * (B h h).re := by linarith
    have h1 := hq ((B g h).re * s)
    have e : 2 * ((B g h).re * s) * (B g h).re + ((B g h).re * s) ^ 2 * (B h h).re =
        (B g h).re ^ 2 * (s * (2 + s * (B h h).re)) := by ring
    rw [e] at h1
    have hx2 : 0 < (B g h).re ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx))
    have hpos : 0 < (B g h).re ^ 2 * (s * (2 + s * (B h h).re)) :=
      mul_pos hx2 (mul_pos hs0 hsy)
    linarith

theorem rh_and_nondeg_of_strictWeilSign (h : StrictWeilSign) :
    RiemannHypothesis ∧ WeilNondegenerate := by
  refine ⟨riemannHypothesis_of_strictWeilSign h, fun g hm hB => ?_⟩
  by_contra hg0
  have h1 := h g hm hg0
  have h2 := hB g hm
  change (B g g).re < 0 at h1
  linarith

theorem strictWeilSign_iff_rh_and_nondeg :
    StrictWeilSign ↔ RiemannHypothesis ∧ WeilNondegenerate :=
  ⟨rh_and_nondeg_of_strictWeilSign, fun h => strictWeilSign_of_rh_nondeg h.1 h.2⟩

/-- For `c ≤ 43/10` the per-packet fine budget is exactly RH together with nondegeneracy. -/
theorem fineBudget_iff_rh_and_nondeg {c : ℝ} (hc : c ≤ 43 / 10) :
    FineBudget c ↔ RiemannHypothesis ∧ WeilNondegenerate :=
  (fineBudget_iff_strictWeilSign hc).trans strictWeilSign_iff_rh_and_nondeg

end AEGIS.WeilStrictSignNondegV1

#print axioms AEGIS.WeilStrictSignNondegV1.re_B_add_scale
#print axioms AEGIS.WeilStrictSignNondegV1.strictWeilSign_of_rh_nondeg
#print axioms AEGIS.WeilStrictSignNondegV1.strictWeilSign_iff_rh_and_nondeg
#print axioms AEGIS.WeilStrictSignNondegV1.fineBudget_iff_rh_and_nondeg
