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

import AEGISOverlay.RHActualLocalGramCoercivityV1

/-!
AEGIS Ω — genuine full-Weil mixed-term defect, without dropped off-diagonals.

The entire finite Gram is the original arithmetic form, not a surrogate.
For every given compact-support local smooth partition we construct genuine
moment-zero narrow atoms with 32/25 diagonal gain and prove the EXACT global
lower bound in terms of the actual mixed contribution.

The remaining universal-sign obligation is precisely control of this
genuine mixed defect. No unconditional RH statement is introduced.
-/

open Set Finset Complex
open scoped ContDiff BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualMixedDefectV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13

/-- Genuine off-diagonal contribution: total B-Gram real part minus all
diagonal real parts. No term is discarded or replaced. -/
def actualMixedDefect (n : ℕ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) : ℝ :=
  (∑ i, ∑ j, B (gs i) (gs j)).re -
    ∑ i, (B (gs i) (gs i)).re

/-- Pure algebraic summation of the original pointwise 32/25 diagonal
coercivity. No mixed-term bound is assumed. -/
theorem quantitative_lower_of_diagonal
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hd : ∀ i, (32 / 25 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re) :
    (32 / 25 : ℝ) * (∑ i, energy (gs i).1) -
      actualMixedDefect n gs ≤
        -(∑ i, ∑ j, B (gs i) (gs j)).re := by
  have hs :
      (∑ i, (32 / 25 : ℝ) * energy (gs i).1) ≤
        ∑ i, -(B (gs i) (gs i)).re :=
    Finset.sum_le_sum (fun i _ => hd i)
  have hdiag :
      (32 / 25 : ℝ) * (∑ i, energy (gs i).1) ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_neg_distrib] using hs
  unfold actualMixedDefect
  linarith

/-- For every arbitrary packet and every feasible locally complete narrow
smooth partition, construct an actual finite Gram and its exact quantitative
mixed-defect lower bound. -/
theorem every_packet_actual_mixed_defect_bound
    (n : ℕ)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (L : ℝ) (hL : 0 ≤ L)
    (hs : tsupport (AEGIS.RHKreinFactorV13.lift g.1) ⊆ Icc (-L) L)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x ∈ Icc (-L) L, ∑ i : Fin (n + 1), χ i x = 1)
    (center : Fin (n + 1) → ℝ)
    (hcut : ∀ i, tsupport (χ i) ⊆
      Icc (center i - 1 / 128) (center i + 1 / 128)) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (32 / 25 : ℝ) * (∑ i, energy (gs i).1) -
          actualMixedDefect n gs ≤
            -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
  obtain ⟨gs, hmom, hd, hpacket, hgram⟩ :=
    AEGIS.RHActualLocalGramCoercivityV1.every_packet_actual_narrow_coercive_gram
      n g hm L hL hs χ hχ hpart center hcut
  refine ⟨gs, hmom, hpacket, ?_⟩
  calc
    (32 / 25 : ℝ) * (∑ i, energy (gs i).1) -
          actualMixedDefect n gs ≤
      -(∑ i, ∑ j, B (gs i) (gs j)).re :=
        quantitative_lower_of_diagonal n gs hd
    _ = -(WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := by
      rw [hgram]

/-- The exact, separately identifiable mixed-term budget that would close
the sign of this *particular* genuine Weil Gram. It is not assumed globally. -/
theorem actual_zero_sign_of_paid_mixed_defect
    (n : ℕ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (hdiag : ∀ i, (32 / 25 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hgram : (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re)
    (hbudget : actualMixedDefect n gs ≤
      (32 / 25 : ℝ) * (∑ i, energy (gs i).1)) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  have hbound := quantitative_lower_of_diagonal n gs hdiag
  have hsign : (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 := by
    rw [hgram]
    linarith
  exact (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
    g hm).mp hsign

end AEGIS.RHActualMixedDefectV1

#print axioms AEGIS.RHActualMixedDefectV1.quantitative_lower_of_diagonal
#print axioms AEGIS.RHActualMixedDefectV1.every_packet_actual_mixed_defect_bound
#print axioms AEGIS.RHActualMixedDefectV1.actual_zero_sign_of_paid_mixed_defect
