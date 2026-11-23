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

-- `Main` is the top module of Levent Alpöge's Lean library (branch `original` of
-- github.com/Deicyde/riemann-hypothesis, Lean v4.33.1, Mathlib 0df444a3); it provides
-- `riemannHypothesis : RiemannHypothesis`.
import Main
import WeilStrictSignMellinV1
import WeilFineChain43V1

/-!
AEGIS Ω × Alpöge — the AEGIS Weil chain made unconditional (Claude Lab, 2026-11-23).

The RH content comes entirely from Alpöge's theorem `riemannHypothesis`. AEGIS contributes the Weil-side
consequences, all proved earlier with RH as an explicit hypothesis:

* `aegis_final_sign`: the repository's final sign residual — `Re W(g ⋆ g) ≤ 0` for every compactly supported
  smooth moment-zero packet (`rh_implies_final_sign_residual_v13`).
* `aegis_zero_quadratic_nonnegative`: the canonical zero quadratic is nonnegative for every packet.
* `aegis_strict_sign_iff_mellin`, `aegis_nondeg_iff_mellin`, `aegis_fineBudget_iff_mellin`: the per-packet fine
  budget, nondegeneracy of the Weil form and the strict Weil sign are each equivalent to
  `MellinZeroNonvanishing`, a statement that no longer involves RH.

`MellinZeroNonvanishing` is still NOT proved.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.AegisAlpogeBridgeV1

open AEGIS.WeilFineBudgetEquivV1 AEGIS.WeilStrictSignNondegV1 AEGIS.WeilStrictSignMellinV1

/-- The AEGIS final sign residual, unconditionally. -/
theorem aegis_final_sign : AEGIS.RHFinalClosureV1.FinalSignResidualV1 :=
  AEGIS.WeilRHImpliesFinalSignV13.rh_implies_final_sign_residual_v13 riemannHypothesis

/-- The Weil sign on every compactly supported smooth moment-zero packet. -/
theorem aegis_weil_sign (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
  aegis_final_sign g hm

/-- The canonical zero quadratic is nonnegative for every packet. -/
theorem aegis_zero_quadratic_nonnegative (g : WeilCompactSmoothGV1) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  AEGIS.WeilRHImpliesFinalSignV13.rh_zero_quadratic_nonnegative_v13 riemannHypothesis g

theorem aegis_strict_sign_iff_mellin : StrictWeilSign ↔ MellinZeroNonvanishing :=
  strictWeilSign_iff_rh_and_mellin.trans (and_iff_right riemannHypothesis)

theorem aegis_nondeg_iff_mellin : WeilNondegenerate ↔ MellinZeroNonvanishing :=
  nondeg_iff_mellin_of_rh riemannHypothesis

theorem aegis_fineBudget_iff_mellin {c : ℝ} (hc : c ≤ 43 / 10) :
    FineBudget c ↔ MellinZeroNonvanishing :=
  (fineBudget_iff_rh_and_mellin hc).trans (and_iff_right riemannHypothesis)

end AEGIS.AegisAlpogeBridgeV1

#print axioms AEGIS.AegisAlpogeBridgeV1.aegis_final_sign
#print axioms AEGIS.AegisAlpogeBridgeV1.aegis_zero_quadratic_nonnegative
#print axioms AEGIS.AegisAlpogeBridgeV1.aegis_fineBudget_iff_mellin
