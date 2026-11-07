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

import AEGISOverlay.RHActualNarrowGramSignV1
import AEGISOverlay.RHActualMixedDefectV1
import AEGISOverlay.RHCofinalSchurAdapterV1

/-!
# Exact genuine Weil two-packet positivity on prime-log-free separations

The source-certified far Archimedean decay and *actual* prime-term vanishing
are combined with the source-proved fine diagonal margin for differently
shaped moment-zero fine packets. There is no fixed distance cutoff in the
theorem syntax. The integer-log avoidance is nevertheless a substantial
geometric restriction, not a global estimate: logarithms of successive
integers become closer than 1/128 beyond index 128. These proofs make NO
claim of arbitrary-distance nonresonance, unrestricted RH positivity, or RH.
-/

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFarPrimeFreeActualGramV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHRationalNinePacketPrimeWindowV1

/-- Genuine Weil-B bound for two unrelated fine packets at *any* distance
avoiding all positive integer logarithms by more than one fine-cell width.
The bound 676/65536 is the original exact rational Arch certificate. -/
theorem prime_free_far_actual_B_q16
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hm : WeilMomentConditionsV1 u)
    (hgap : (35 / 128 : ℝ) ≤ b - a)
    (havoid : ∀ m : ℕ, 0 < m →
      (1 / 128 : ℝ) < |Real.log (m : ℝ) - (b - a)|) :
    ‖B u v‖ ≤ (676 / 65536 : ℝ) * (energy u.1 + energy v.1) := by
  have hactual :=
    AEGIS.RHActualMixedDefectV1.distinct_fine_actual_B_of_integer_log_gap
      u v a b hu hv hm (by linarith) havoid
  have harch := AEGIS.RHActualMixedDefectV1.moment_zero_fine_middle_arch_q16
    ((b - a) - 1 / 128) (by linarith)
  exact hactual.trans (mul_le_mul_of_nonneg_right harch
    (add_nonneg (energy_nonnegative u.1) (energy_nonnegative v.1)))

/-- An actual nonlocal two-packet Gram has margin at least total energy.
No same-mother restriction, no hypothesis about the sign of B(u,v).
All prime powers are present but source-proven zero by the log-gap predicate. -/
theorem prime_free_far_two_packet_actual_gram_margin
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hmU : WeilMomentConditionsV1 u)
    (hgap : (35 / 128 : ℝ) ≤ b - a)
    (havoid : ∀ m : ℕ, 0 < m →
      (1 / 128 : ℝ) < |Real.log (m : ℝ) - (b - a)|) :
    (B (addPacket u v) (addPacket u v)).re ≤
      -(energy u.1 + energy v.1) := by
  have hdiagU := AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3 u a hu
  have hdiagV := AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3 v b hv
  have hnorm := prime_free_far_actual_B_q16 u v a b hu hv hmU hgap havoid
  have hcross : (B u v).re ≤
      (676 / 65536 : ℝ) * (energy u.1 + energy v.1) :=
    (Complex.re_le_norm _).trans hnorm
  have hsum : (0 : ℝ) ≤ energy u.1 + energy v.1 :=
    add_nonneg (energy_nonnegative u.1) (energy_nonnegative v.1)
  have hgram := AEGIS.RHCofinalSchurAdapterV1.actual_two_block_gram_coefficients u v
  linarith

/-- The SAME actual nonlocal pair has a genuine zeta-zero quadratic margin
of at least the total source energy, not just an abstract matrix sign. -/
theorem prime_free_far_two_packet_actual_zero_margin
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hu : WidthOneOneTwentyEightAt u a)
    (hv : WidthOneOneTwentyEightAt v b)
    (hmU : WeilMomentConditionsV1 u)
    (hmV : WeilMomentConditionsV1 v)
    (hgap : (35 / 128 : ℝ) ≤ b - a)
    (havoid : ∀ m : ℕ, 0 < m →
      (1 / 128 : ℝ) < |Real.log (m : ℝ) - (b - a)|) :
    energy u.1 + energy v.1 ≤
      (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1
          (WeilAutocorrelationV1 (addPacket u v)) rho).re := by
  have hm : WeilMomentConditionsV1 (addPacket u v) :=
    AEGIS.WeilFinalSignTranslationBoundV10.momentConditions_addPacket_v10 u v hmU hmV
  have hreal := prime_free_far_two_packet_actual_gram_margin
    u v a b hu hv hmU hgap havoid
  have hEF :=
    AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10
      (addPacket u v) hm
  have hre := congrArg Complex.re hEF
  simp only [Complex.neg_re] at hre
  change (B (addPacket u v) (addPacket u v)).re =
    -(∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1
        (WeilAutocorrelationV1 (addPacket u v)) rho).re at hre
  linarith

end AEGIS.RHFarPrimeFreeActualGramV1

#print axioms AEGIS.RHFarPrimeFreeActualGramV1.prime_free_far_actual_B_q16
#print axioms AEGIS.RHFarPrimeFreeActualGramV1.prime_free_far_two_packet_actual_gram_margin
#print axioms AEGIS.RHFarPrimeFreeActualGramV1.prime_free_far_two_packet_actual_zero_margin