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

import AEGISOverlay.RHKreinMultiplicativeTransportV1
import RHCofinalSchurAdapterV1
import RHRestrictedWeilBridgeV13
import Mathlib.Tactic
import AEGISOverlay.RHSignedPrimeChebyshevFiniteBridgeV6
import AEGISOverlay.RHOptimizedSchurGlobalJoinV1

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

open scoped ContDiff BigOperators ContDiff
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

/-! ## Selected Krein-Feshbach compatibility wrappers (one implementation) -/

/-- Stable public name; the implementing producer is now on the source-bound
Krein transport lane, compiled by the existing cofinal Schur workflow. -/
abbrev SelectedKreinFeshbachProducerV2 : Prop :=
  AEGIS.RHKreinMultiplicativeTransportV1.SelectedKreinFeshbachProducerV2

/-- Every old all-decompositions producer supplies a selected producer.
The reverse implication is not claimed. -/
theorem selected_krein_feshbach_of_universal_v2
    (h : UniversalKreinFeshbachProducerV1) :
    SelectedKreinFeshbachProducerV2 := by
  intro g hm
  obtain ⟨χ, hχ, hproducer⟩ := h g hm
  obtain ⟨u, v, hu, hv, hsum, _⟩ :=
    every_packet_actual_two_block_zero_quadratic g hm χ hχ
  exact ⟨u, v, hu, hv, hsum, hproducer u v hu hv hsum⟩

/-- Thin compatibility wrapper: the proof term lives with the source
reconstruction and genuine two-block identity. -/
theorem universal_of_selected_krein_feshbach_producer_v2
    (hselect : SelectedKreinFeshbachProducerV2) :
    UniversalZeroQuadraticNonnegativeV10 :=
  AEGIS.RHKreinMultiplicativeTransportV1.universal_of_selected_krein_feshbach_producer_v2
    hselect

/-- Stable terminal name, preserving exactly the original conditional goal. -/
theorem riemannHypothesis_of_selected_krein_feshbach_producer_v2
    (hselect : SelectedKreinFeshbachProducerV2) : RiemannHypothesis :=
  AEGIS.RHKreinMultiplicativeTransportV1.riemannHypothesis_of_selected_krein_feshbach_producer_v2
    hselect

/-- The final canonical Mathlib RH goal, assembled from existing verified
implications with no extra axioms. The producer remains an explicit premise. -/
theorem riemannHypothesis_of_krein_feshbach_producer_v1
    (h : UniversalKreinFeshbachProducerV1) : RiemannHypothesis :=
  AEGIS.RHRestrictedWeilBridgeV13.restricted_weil_criterion_kernel_bridge_v13
    (universal_of_krein_feshbach_producer_v1 h)


/-! ## Exact cross-carrier reuse: Abel/Chebyshev → signed-prime → RH → Krein/Weil

The finite Abel-Chebyshev result V6 and the signed-prime/zero-kernel V5
are consumed by their exact theorem names. The resulting canonical RH
criterion is transported into the EXISTING actual finite mixed Gram carrier.
This joins two previously separate routes without new axioms, surrogate
forms, artificial reconstruction hypotheses, or extra certificate fields.
V6's two analytic closure inputs and the genuine prime-only growth input
remain explicit; this source composition alone is not unconditional RH.
-/

/-- The original V6 and V5 theorem statements compose at the SAME fixed
detecting packet; no new dictionary or named mathematical assumption. -/
theorem riemannHypothesis_of_existing_abel_prime_chain_v1
    (hExtend :
      AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6.EventuallyChebyshevFiniteIntegralExtendsV6)
    (hIntegrable :
      AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6.EventuallyArithmeticConvolutionsIntegrableV6)
    (hPrime : AEGIS.RHSubexpBoundedPerturbationV1.SubexponentialAtTopV1
      (AEGIS.RHPrimeOnlyGrowthBridgeV1.primeOnlyOrbitV1
        AEGIS.RHFixedPacketFrontierV1.detectingPacket)) :
    RiemannHypothesis :=
  AEGIS.RHSignedPrimeActualKernelTailV5.riemannHypothesis_of_signed_dictionary_and_prime_growth
    (AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6.eventual_signed_prime_equals_combined_of_analytic_closure
      hExtend hIntegrable) hPrime

/-- SOURCE-COMPATIBLE cross-route handoff:
the prime/Abel carrier fills the exact *signed actual Weil Gram* interface
already used by the unconditional Krein fine-partition constructor.
The only assumptions are inherited unchanged from the prior V6/V5 route. -/
theorem actual_fine_signed_gram_of_abel_prime_v1
    (hExtend :
      AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6.EventuallyChebyshevFiniteIntegralExtendsV6)
    (hIntegrable :
      AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6.EventuallyArithmeticConvolutionsIntegrableV6)
    (hPrime : AEGIS.RHSubexpBoundedPerturbationV1.SubexponentialAtTopV1
      (AEGIS.RHPrimeOnlyGrowthBridgeV1.primeOnlyOrbitV1
        AEGIS.RHFixedPacketFrontierV1.detectingPacket)) :
    ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
      ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
        g = AEGIS.RHGramExpansionV13.packetSum (fun _ => (1 : ℂ)) gs ∧
        AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
          -(∑ i, (AEGIS.WeilMixedAlgebraV2.B (gs i) (gs i)).re) :=
  AEGIS.RHOptimizedSchurGlobalJoinV1.rh_iff_one_actual_sharp_signed_budget.mp
    (riemannHypothesis_of_existing_abel_prime_chain_v1 hExtend hIntegrable hPrime)

end AEGIS.RHKreinFeshbachFinalAssemblyV1

#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.universal_of_krein_signed_budget_v1
#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.universal_of_krein_feshbach_producer_v1
#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.riemannHypothesis_of_krein_feshbach_producer_v1

#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.riemannHypothesis_of_existing_abel_prime_chain_v1
#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.actual_fine_signed_gram_of_abel_prime_v1

#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.selected_krein_feshbach_of_universal_v2
#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.universal_of_selected_krein_feshbach_producer_v2
#print axioms AEGIS.RHKreinFeshbachFinalAssemblyV1.riemannHypothesis_of_selected_krein_feshbach_producer_v2
