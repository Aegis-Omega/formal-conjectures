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

import RHMomentDecayCofinalJoinV1
import RHFeshbachWeilClosureV2
import RHRestrictedWeilBridgeV13

/-!
AEGIS Ω — cofinal actual-zero terminal, using the October 14 moment-decay join.
The all-packets cofinal certificate remains an explicit premise.
-/

open Filter Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHCofinalActualTerminalV1

/-- For each actual moment-zero packet, a single cofinal approximant sequence
carries the zero sum, norm convergence and the genuine N^-4 lower bound. -/
def EveryPacketCofinalLowerCertificate : Prop :=
  ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
    ∃ (N : ℕ → ℕ) (q normSq : ℕ → ℝ) (normSqLimit : ℝ),
      Tendsto N atTop atTop ∧
      Tendsto q atTop
        (𝓝 ((∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re)) ∧
      Tendsto normSq atTop (𝓝 normSqLimit) ∧
      (∀ j : ℕ,
        -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
          normSq j ≤ q j)

/-- Reuse the kernel-checked cofinal lower-bound transfer without rebuilding it. -/
theorem universal_of_cofinal_lower_certificates
    (h : EveryPacketCofinalLowerCertificate) :
    AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10 := by
  intro g hm
  obtain ⟨N, q, normSq, normSqLimit, hN, hq, hnorm, hlower⟩ := h g hm
  exact AEGIS.RHMomentDecayCofinalJoinV1.actual_zero_quadratic_nonnegative_of_cofinal_lower_bound
    g hN hq hnorm hlower

/-- The real Mathlib target; the all-packets certificate is still required. -/
theorem riemannHypothesis_of_cofinal_lower_certificates
    (h : EveryPacketCofinalLowerCertificate) : RiemannHypothesis :=
  AEGIS.RHRestrictedWeilBridgeV13.restricted_weil_criterion_kernel_bridge_v13
    (universal_of_cofinal_lower_certificates h)

/-- The existing cofinal-certificate proposition is exactly RH-equivalent.
The reverse implication chooses the constant true zero-quadratic and zero
"norm" sequence. The present certificate definition does NOT bind that
sequence to the norm of any actual approximant. This theorem is a diagnostic
of the current proposition, not an unconditional proof of RH. -/
theorem cofinal_lower_certificates_iff_riemannHypothesis :
    EveryPacketCofinalLowerCertificate ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_cofinal_lower_certificates
  · intro hRH g hm
    have hzero :
        0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re :=
      (AEGIS.WeilRHImpliesFinalSignV13.rh_implies_universal_v13 hRH) g hm
    refine ⟨(fun j : ℕ => j),
      (fun _ => (∑' rho : RiemannNontrivialZeroIndexV2,
        WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re),
      (fun _ => (0 : ℝ)), 0,
      ?_, ?_, ?_, ?_⟩
    · exact tendsto_id
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · intro j
      simpa using hzero

end AEGIS.RHCofinalActualTerminalV1

#print axioms AEGIS.RHCofinalActualTerminalV1.universal_of_cofinal_lower_certificates
#print axioms AEGIS.RHCofinalActualTerminalV1.riemannHypothesis_of_cofinal_lower_certificates
#print axioms AEGIS.RHCofinalActualTerminalV1.cofinal_lower_certificates_iff_riemannHypothesis
