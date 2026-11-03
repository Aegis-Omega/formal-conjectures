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

import RHKreinMultiplicativeTransportV1
import RHCofinalSchurAdapterV1
import RHRestrictedWeilBridgeV13
import Mathlib.Tactic

/-!
# AEGIS Ω: actual Krein decomposition → actual Feshbach bound → canonical RH

This joins existing, source-bound results:
* finite Krein transport with exact reconstruction and both zero moments;
* the exact two-block arithmetic Weil/zero-side equality;
* the genuine mixed-block Feshbach lower bound;
* the V13 criterion for Mathlib's `RiemannHypothesis`.

The only open analytic input is explicitly named below. No assumption is
silently supplied and no finite-window certificate is promoted to all windows.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinFeshbachFinalAssemblyV1

open AEGIS.RHKreinMultiplicativeTransportV1
open AEGIS.RHMillenniumGateV10

/-- A source-bound, universal *signed* mixed-entry budget on one Krein
partition of each actual moment-zero Weil packet. This is a global
mathematical obligation, not a completed certificate. -/
def UniversalKreinTwoBlockSignedBudgetV1 : Prop :=
  ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
    ∃ χ : ℝ → ℂ, ContDiff ℝ ∞ χ ∧
      ∀ u v : WeilCompactSmoothGV1,
        WeilMomentConditionsV1 u →
        WeilMomentConditionsV1 v →
        g = AEGIS.WeilMixedAlgebraV2.addPacket u v →
        0 ≤
          -(AEGIS.WeilMixedAlgebraV2.B u u).re +
          2 * (-(AEGIS.WeilMixedAlgebraV2.B u v).re) +
          -(AEGIS.WeilMixedAlgebraV2.B v v).re

/-- Exact Krein reconstruction and the genuine Weil mixed identity
reduce the universal zero-side sign to the signed-entry producer. -/
theorem universal_of_krein_signed_budget_v1
    (h : UniversalKreinTwoBlockSignedBudgetV1) :
    UniversalZeroQuadraticNonnegativeV10 := by
  intro g hm
  obtain ⟨χ, hχ, hbudget⟩ := h g hm
  obtain ⟨u, v, hu, hv, hsum, hzero⟩ :=
    every_packet_actual_two_block_zero_quadratic g hm χ hχ
  have hsigned := hbudget u v hu hv hsum
  rw [hzero]
  exact hsigned

/-- Concrete Schur/Feshbach data for every actual two-block Krein
reconstruction, retaining the true diagonal, tail and mixed Weil entries.
The nonnegative Schur remainder must be proved analytically. -/
def UniversalKreinFeshbachProducerV1 : Prop :=
  ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
    ∃ χ : ℝ → ℂ, ContDiff ℝ ∞ χ ∧
      ∀ u v : WeilCompactSmoothGV1,
        WeilMomentConditionsV1 u →
        WeilMomentConditionsV1 v →
        g = AEGIS.WeilMixedAlgebraV2.addPacket u v →
        ∃ nv nw β c μ : ℝ,
          0 ≤ nw ∧
          c * nw ^ 2 ≤ -(AEGIS.WeilMixedAlgebraV2.B v v).re ∧
          (-(AEGIS.WeilMixedAlgebraV2.B u v).re) ^ 2 ≤ β * nw ^ 2 ∧
          0 ≤ β ∧
          μ < c ∧
          0 ≤ μ ∧
          0 ≤
            -(AEGIS.WeilMixedAlgebraV2.B u u).re -
              μ * nv ^ 2 - β / (c - μ)

/-- The repository's established Feshbach estimate discharges the
signed budget whenever the exact universal Schur producer is available. -/
theorem universal_of_krein_feshbach_producer_v1
    (h : UniversalKreinFeshbachProducerV1) :
    UniversalZeroQuadraticNonnegativeV10 := by
  intro g hm
  obtain ⟨χ, hχ, hproducer⟩ := h g hm
  obtain ⟨u, v, hu, hv, hsum, _⟩ :=
    every_packet_actual_two_block_zero_quadratic g hm χ hχ
  obtain ⟨nv, nw, β, c, μ, hnw, htail, hcross, hβ, hgap, hμ, hschur⟩ :=
    hproducer u v hu hv hsum
  have hmuv :
      WeilMomentConditionsV1 (AEGIS.WeilMixedAlgebraV2.addPacket u v) := by
    simpa only [hsum] using hm
  have hschur0 :
      -(0 : ℝ) * 0 ≤
        -(AEGIS.WeilMixedAlgebraV2.B u u).re -
          μ * nv ^ 2 - β / (c - μ) := by
    simpa only [neg_zero, zero_mul] using hschur
  have hz := AEGIS.RHCofinalSchurAdapterV1.actual_two_block_zero_quadratic_schur_bound
    u v hmuv nv nw β c μ 0 0 hnw htail hcross hβ hgap hμ hschur0
  rw [hsum]
  simpa only [neg_zero, zero_mul] using hz

/-- The final canonical Mathlib RH goal, assembled from existing verified
implications with no extra axioms. The producer remains an explicit premise. -/
theorem riemannHypothesis_of_krein_feshbach_producer_v1
    (h : UniversalKreinFeshbachProducerV1) : RiemannHypothesis :=
  AEGIS.RHRestrictedWeilBridgeV13.restricted_weil_criterion_kernel_bridge_v13
    (universal_of_krein_feshbach_producer_v1 h)

end AEGIS.RHKreinFeshbachFinalAssemblyV1

#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.universal_of_krein_signed_budget_v1
#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.universal_of_krein_feshbach_producer_v1
#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.riemannHypothesis_of_krein_feshbach_producer_v1
