import WeilStrictSignMellinV1
import WeilFineChain43V1
open AEGIS.WeilFineBudgetEquivV1 AEGIS.WeilStrictSignNondegV1 AEGIS.WeilStrictSignMellinV1
-- Same terms as AegisAlpogeBridgeV1, with Alpöge's `riemannHypothesis` replaced by a hypothesis `hRH`.
example (hRH : RiemannHypothesis) : AEGIS.RHFinalClosureV1.FinalSignResidualV1 :=
  AEGIS.WeilRHImpliesFinalSignV13.rh_implies_final_sign_residual_v13 hRH
example (hRH : RiemannHypothesis) (g : WeilCompactSmoothGV1) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2, WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
  AEGIS.WeilRHImpliesFinalSignV13.rh_zero_quadratic_nonnegative_v13 hRH g
example (hRH : RiemannHypothesis) : StrictWeilSign ↔ MellinZeroNonvanishing :=
  strictWeilSign_iff_rh_and_mellin.trans (and_iff_right hRH)
example (hRH : RiemannHypothesis) : WeilNondegenerate ↔ MellinZeroNonvanishing := nondeg_iff_mellin_of_rh hRH
example (hRH : RiemannHypothesis) {c : ℝ} (hc : c ≤ 43 / 10) : FineBudget c ↔ MellinZeroNonvanishing :=
  (fineBudget_iff_rh_and_mellin hc).trans (and_iff_right hRH)
example (hRH : RiemannHypothesis) (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
  AEGIS.WeilRHImpliesFinalSignV13.rh_implies_final_sign_residual_v13 hRH g hm
