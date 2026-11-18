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

import AEGISOverlay.RHGlobalPrimeArchFrontierV1
import RHConsolidatedV1

/-!
# Actual prime/Arch Weil sign on the kernel-certified range

The first theorem transfers a source-bound 317-module finite-window
certificate to the real prime/Arch expression, without assuming RH.
The other two theorems expose the remaining genuinely global premise.
They do not constitute an unconditional proof of RiemannHypothesis.
-/

open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHGlobalPrimeArchConsolidatedJoinV1

open AEGIS.RHGlobalPrimeArchFrontierV1
open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.WeilWindowExhaustionV1

/-- Actual prime-versus-Archimedean inequality for every moment-zero Weil
packet within the 317-module kernel-certified log window. -/
theorem prime_arch_domination_on_certified_windows
    {L : ℝ} (h0 : 0 ≤ L) (hsmall : L < 21 / 40)
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (hw : LogWindowContainsV1 g L) :
    (WeilPrimeSumV1 (WeilAutocorrelationV1 g)).re ≤
      (1 / (4 * Real.pi)) *
        ∫ t : ℝ, archSymbol t * criticalSpectralMass g t := by
  have hsign : (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
    AEGIS.RHConsolidatedV1.windows_below_21_40 L h0 hsmall g hm hw
  rw [actual_arithmetic_real_eq_prime_sub_archSymbol] at hsign
  exact sub_nonpos.mp hsign

/-- Real global prime/Arch control is exactly the unsigned-window obligation
remaining after the 317-module checkpoint, not a consequence of its finite
window certificates. -/
theorem global_prime_arch_iff_remaining_windows :
    GlobalPrimeArchDomination ↔
      ∀ L : ℝ, 21 / 40 ≤ L → WindowArithmeticNonpositiveV1 L := by
  constructor
  · intro h L _ g hm _
    have hz := (global_prime_arch_iff_universal.mp h) g hm
    exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mpr hz
  · intro h g hm
    obtain ⟨L, hL, hw⟩ := logLift_has_finite_window_v1 g
    have hsign :
        (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 := by
      by_cases hsmall : L < 21 / 40
      · exact AEGIS.RHConsolidatedV1.windows_below_21_40 L hL.le hsmall g hm hw
      · exact h L (le_of_not_gt hsmall) g hm hw
    rw [actual_arithmetic_real_eq_prime_sub_archSymbol] at hsign
    exact sub_nonpos.mp hsign

/-- Global prime/Arch control and the canonical RH proposition are equivalent;
an independent proof of the global inequality is still OPEN. -/
theorem global_prime_arch_iff_riemannHypothesis :
    GlobalPrimeArchDomination ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_global_prime_arch
  · intro h
    exact global_prime_arch_iff_remaining_windows.mpr
      (AEGIS.RHConsolidatedV1.rh_iff_windows_from_21_40.mp h)

end AEGIS.RHGlobalPrimeArchConsolidatedJoinV1

#print axioms AEGIS.RHGlobalPrimeArchConsolidatedJoinV1.prime_arch_domination_on_certified_windows
#print axioms AEGIS.RHGlobalPrimeArchConsolidatedJoinV1.global_prime_arch_iff_remaining_windows
#print axioms AEGIS.RHGlobalPrimeArchConsolidatedJoinV1.global_prime_arch_iff_riemannHypothesis