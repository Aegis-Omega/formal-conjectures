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

import AEGISOverlay.RHActualUniversalFineGramV1
import AEGISOverlay.RHGlobalPrimeArchFrontierV1

/-!
# Exact global prime/Arch control retaining the signed mixed residual

For every admissible moment-zero Weil packet, a genuine finite family of
moment-zero atoms exists, and the arithmetic prime/Arch gap is bounded by the
source-derived diagonal energy and actual mixed Gram defect.

These unconditional estimates retain the signed defect. No global sign
claim or RH proof is inferred without bounding that defect.
-/

open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHGlobalPrimeArchFineGramControlV1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13
open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHGlobalPrimeArchFrontierV1

/-- An unconditional actual fine-Gram representation and prime/Arch bound for
each original smooth moment-zero Weil packet, with the full mixed term. -/
theorem global_arch_prime_lower_bound_of_actual_fine_gram
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) -
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
        (1 / (4 * Real.pi)) *
          ∫ t : ℝ, archSymbol t * criticalSpectralMass g t -
        (WeilPrimeSumV1 (WeilAutocorrelationV1 g)).re := by
  obtain ⟨n, gs, hmom, hpacket, hbound⟩ :=
    AEGIS.RHActualUniversalFineGramV1.every_packet_actual_fine_mixed_defect_lower_bound g hm
  refine ⟨n, gs, hmom, hpacket, ?_⟩
  rw [actual_arithmetic_real_eq_prime_sub_archSymbol] at hbound
  simpa only [neg_sub] using hbound

/-- Equivalent prime-side formulation. The real mixed Weil defect is retained
rather than replaced by its absolute value or an unjustified sign. -/
theorem global_prime_arch_with_signed_error
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      g = packetSum (fun _ => (1 : ℂ)) gs ∧
      (WeilPrimeSumV1 (WeilAutocorrelationV1 g)).re ≤
        (1 / (4 * Real.pi)) *
          ∫ t : ℝ, archSymbol t * criticalSpectralMass g t +
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs -
        (5671 / 3200 : ℝ) * (∑ i, energy (gs i).1) := by
  obtain ⟨n, gs, hmom, hpacket, hlower⟩ :=
    global_arch_prime_lower_bound_of_actual_fine_gram g hm
  refine ⟨n, gs, hmom, hpacket, ?_⟩
  have rearrange (p a e d : ℝ) (h : e - d ≤ a - p) :
      p ≤ a + d - e := by
    linarith only [h]
  exact rearrange _ _ _ _ hlower

end AEGIS.RHGlobalPrimeArchFineGramControlV1

#print axioms AEGIS.RHGlobalPrimeArchFineGramControlV1.global_arch_prime_lower_bound_of_actual_fine_gram
#print axioms AEGIS.RHGlobalPrimeArchFineGramControlV1.global_prime_arch_with_signed_error
