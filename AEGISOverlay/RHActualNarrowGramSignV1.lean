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

import RHFiniteActualGramJoinV1
import RHWindow693Over2000V1
import RHKreinTrigramAdaptiveV1

/-!
# Actual (not surrogate) finite Weil Gram sign on the certified window

This combines two existing independent *unconditional* Lean results:
* every moment-zero Weil packet admits an exact genuine finite Gram
  decomposition for ANY smooth partition of unity, preserving every mixed term;
* the actual arithmetic Weil form is nonpositive for every admissible packet
  of logarithmic half-width 693/2000.

For every such packet, every smooth partition yields genuine moment-zero
packets whose FULL actual Weil Hermitian Gram contraction has the certified
sign, without assuming any off-diagonal estimate or dropping B(i,j).

It does NOT establish that a weighted span of these partition atoms stays
within the certified class, nor PSD of arbitrary large-support packets.
-/

open scoped ContDiff BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualNarrowGramSignV1

open AEGIS.WeilMixedAlgebraV2

/-- Exact full-matrix sign with every mixed coefficient retained, for any
smooth finite partition of an admissible packet in the certified 693/2000
window. This is NOT a global all-support RH positivity theorem. -/
theorem every_narrow_packet_actual_full_gram_nonpositive
    (n : ℕ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g (693 / 2000))
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x : ℝ, ∑ i : Fin (n + 1), χ i x = 1) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∑ i, ∑ j, B (gs i) (gs j)).re ≤ 0 := by
  obtain ⟨gs, hgs, hfull⟩ :=
    AEGIS.RHFiniteActualGramJoinV1.every_packet_actual_finite_gram
      n g hm χ hχ hpart
  refine ⟨gs, hgs, ?_⟩
  calc
    (∑ i, ∑ j, B (gs i) (gs j)).re =
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := hfull.symm
    _ ≤ 0 :=
      AEGIS.RHWindow693Over2000V1.window_693_over_2000_arithmetic_nonpositive_v1
        g hm hw


/-- The exact genuine Weil Gram contraction of ANY finite smooth partition
of a two-moment packet on the larger Trigram 2/5 logarithmic window is
nonpositive.  All cross terms B(gs i, gs j) remain in the conclusion:
nothing is dropped, averaged, or bounded by a surrogate coefficient.

This reuses the fully constructive moment-zero Krein partition and the
original actual arithmetic Trigram sign, with no added analytic premise.
It does NOT claim the same sign for packets of arbitrary support. -/
theorem every_two_fifths_packet_actual_full_gram_nonpositive
    (n : ℕ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g (2 / 5))
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x : ℝ, ∑ i : Fin (n + 1), χ i x = 1) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∑ i, ∑ j, B (gs i) (gs j)).re ≤ 0 := by
  obtain ⟨gs, hgs, hfull⟩ :=
    AEGIS.RHFiniteActualGramJoinV1.every_packet_actual_finite_gram
      n g hm χ hχ hpart
  refine ⟨gs, hgs, ?_⟩
  calc
    (∑ i, ∑ j, B (gs i) (gs j)).re =
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := hfull.symm
    _ ≤ 0 :=
      AEGIS.RHKreinTrigramAdaptiveV1.window_two_fifths_trigram_v1 g hm hw

end AEGIS.RHActualNarrowGramSignV1

#print axioms AEGIS.RHActualNarrowGramSignV1.every_narrow_packet_actual_full_gram_nonpositive
#print axioms AEGIS.RHActualNarrowGramSignV1.every_two_fifths_packet_actual_full_gram_nonpositive
