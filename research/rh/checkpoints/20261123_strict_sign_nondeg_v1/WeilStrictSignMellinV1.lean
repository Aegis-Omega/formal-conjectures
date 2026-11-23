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

import WeilStrictSignNondegV1
import RestrictedWeilCriterionResidueCoefficientV11

/-!
AEGIS Ω — the strict Weil sign through the zeros (Claude Lab, 2026-11-23).

`MellinZeroNonvanishing`: the Mellin transform of every nonzero moment-zero packet is nonzero at SOME
nontrivial zero of `ζ`.

Under RH, `−Re W(g ⋆ g) = Σ_ρ m(ρ) |M g(ρ)|²` (`autocorrelation_explicit_formula_v10`,
`rh_zero_summand_eq_normSq_v13`), and every multiplicity is positive (`zeta_analyticOrderNatAt_ne_zero_v11`).

* `strictWeilSign_of_rh_mellin`, `mellin_of_strictWeilSign`,
  `strictWeilSign_iff_rh_and_mellin`: `StrictWeilSign ↔ RH ∧ MellinZeroNonvanishing`.
* `nondeg_iff_mellin_of_rh`: under RH, `WeilNondegenerate ↔ MellinZeroNonvanishing`.
* `fineBudget_iff_rh_and_mellin`: for `c ≤ 43/10`, the per-packet fine budget is RH together with
  `MellinZeroNonvanishing`.

`MellinZeroNonvanishing` is NOT proved here. Not RH.
-/

open Set Finset Complex
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilStrictSignMellinV1

open AEGIS.WeilMixedAlgebraV2 AEGIS.WeilFineBudgetEquivV1 AEGIS.WeilStrictSignNondegV1

/-- Every nonzero moment-zero packet has a Mellin transform that is nonzero at some nontrivial zero. -/
def MellinZeroNonvanishing : Prop :=
  ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g → g.1 ≠ 0 →
    ∃ rho : RiemannNontrivialZeroIndexV2, mellin g.1 rho.1 ≠ 0

theorem strictWeilSign_of_rh_mellin (hRH : RiemannHypothesis) (hM : MellinZeroNonvanishing) :
    StrictWeilSign := by
  intro g hm hg0
  obtain ⟨rho, hrho⟩ := hM g hm hg0
  have hsum : Summable (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g)) :=
    weil_compact_smooth_zero_summable_v1 (WeilAutocorrelationCompactSmoothV1 g)
  have hEF := AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10 g hm
  rw [hEF, Complex.neg_re, Complex.re_tsum hsum]
  have hterm : ∀ r : RiemannNontrivialZeroIndexV2,
      (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) r).re =
        (analyticOrderNatAt riemannZeta r.1 : ℝ) * Complex.normSq (mellin g.1 r.1) := by
    intro r
    rw [AEGIS.WeilRHImpliesFinalSignV13.rh_zero_summand_eq_normSq_v13 hRH g r, Complex.ofReal_re]
  have hsumre : Summable (fun r : RiemannNontrivialZeroIndexV2 =>
      (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) r).re) := by
    simpa using Complex.reCLM.summable hsum
  have hpos : 0 < ∑' r : RiemannNontrivialZeroIndexV2,
      (WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) r).re := by
    refine hsumre.tsum_pos (fun r => ?_) rho ?_
    · rw [hterm]
      exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
    · rw [hterm]
      have hmul : (0 : ℝ) < analyticOrderNatAt riemannZeta rho.1 := by
        exact_mod_cast Nat.pos_of_ne_zero
          (AEGIS.RestrictedWeilCriterionResidueCoefficientV11.zeta_analyticOrderNatAt_ne_zero_v11 rho)
      exact mul_pos hmul (Complex.normSq_pos.mpr hrho)
  linarith

theorem mellin_of_strictWeilSign (h : StrictWeilSign) : MellinZeroNonvanishing := by
  have hRH := riemannHypothesis_of_strictWeilSign h
  intro g hm hg0
  by_contra hall
  have hall' : ∀ r : RiemannNontrivialZeroIndexV2, mellin g.1 r.1 = 0 := fun r => by
    by_contra hne
    exact hall ⟨r, hne⟩
  have hz : ∀ r : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) r = 0 := by
    intro r
    rw [AEGIS.WeilRHImpliesFinalSignV13.rh_zero_summand_eq_normSq_v13 hRH g r, hall' r]
    simp
  have h1 := h g hm hg0
  rw [AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10 g hm] at h1
  have hz' : WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) = fun _ => 0 := funext hz
  simp [hz'] at h1

theorem strictWeilSign_iff_rh_and_mellin :
    StrictWeilSign ↔ RiemannHypothesis ∧ MellinZeroNonvanishing :=
  ⟨fun h => ⟨riemannHypothesis_of_strictWeilSign h, mellin_of_strictWeilSign h⟩,
    fun h => strictWeilSign_of_rh_mellin h.1 h.2⟩

/-- Under RH, nondegeneracy of the Weil form is exactly nonvanishing at some zero. -/
theorem nondeg_iff_mellin_of_rh (hRH : RiemannHypothesis) :
    WeilNondegenerate ↔ MellinZeroNonvanishing :=
  ⟨fun hN => mellin_of_strictWeilSign (strictWeilSign_of_rh_nondeg hRH hN),
    fun hM => (strictWeilSign_iff_rh_and_nondeg.mp (strictWeilSign_of_rh_mellin hRH hM)).2⟩

/-- For `c ≤ 43/10` the per-packet fine budget is RH together with `MellinZeroNonvanishing`. -/
theorem fineBudget_iff_rh_and_mellin {c : ℝ} (hc : c ≤ 43 / 10) :
    FineBudget c ↔ RiemannHypothesis ∧ MellinZeroNonvanishing :=
  (fineBudget_iff_strictWeilSign hc).trans strictWeilSign_iff_rh_and_mellin

end AEGIS.WeilStrictSignMellinV1

#print axioms AEGIS.WeilStrictSignMellinV1.strictWeilSign_iff_rh_and_mellin
#print axioms AEGIS.WeilStrictSignMellinV1.nondeg_iff_mellin_of_rh
#print axioms AEGIS.WeilStrictSignMellinV1.fineBudget_iff_rh_and_mellin
