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

import RHSignedPrimeIntervalExtensionV8
import RHCertifiedApproximationV1
import AEGISOverlay.RHWeilTiltComplementarityV1
import RHLocalKreinPartitionV1
import RHFeshbachCoreV1
import FormalConjecturesUtil.FixedWindowLimitBridge
import WeilWindowExhaustionV1
import WeilRHImpliesFinalSignV13
import RHFinalClosureSpineV1
import Mathlib

/-!
# AEGIS: exact-source RH proof fusion

This is a composition module, not an RH axiom or a claimed unconditional proof.
It joins previously separate, already formalized source paths:

1. V8's unconditional Abel/Chebyshev dictionary with the V5 signed-prime
   eventual-bound criterion.  The resulting equivalent criterion is about the
   *actual* combined arithmetic orbit and then its prime-only component.
2. The PR7 cofinal N^(-4) limit theorem with the actual Feshbach/Schur lower
   inequality, including the exact convergent norm and quadratic-form inputs.
3. The cofinal pi-window bridge with the genuine Weil/RH criterion.
4. The unconditional complementary moment-zero packet pair with the V8
   dictionary (both outputs are preserved, not promoted to a sign estimate).

No new nonstandard axiom, sorry, theorem weakening, or hidden RH assumption.
The predicates on the right of the equivalences still require proof to obtain
an unconditional RH theorem.
-/

open Filter Topology

namespace AEGIS.RHExistingProofFusionV1

open AEGIS.RHFixedPacketFrontierV1
open AEGIS.RHPrimeOnlyGrowthBridgeV1
open AEGIS.RHSubexpBoundedPerturbationV1
open AEGIS.RHSignedPrimeActualKernelTailV5
open AEGIS.RHSignedPrimeIntervalExtensionV8

/-- Unconditionally recovered signed-prime dictionary and its reflected
zero-kernel tail bound. -/
theorem signed_dictionary_and_reflected_tail :
    EventuallySignedPrimeEqualsCombinedOrbitV5 ∧
    AEGIS.RHPrimeOnlyReflectedTailV3.EventuallyReflectedFixedKernelArithmeticRemainderBoundedV3 :=
  ⟨eventual_signed_prime_equals_combined_v8,
   eventual_reflected_kernel_remainder_bounded_v8⟩

/-- The genuine combined arithmetic orbit is eventually bounded precisely when
Mathlib's RiemannHypothesis holds. The V8 dictionary is now a theorem, not an
extra premise. -/
theorem rh_iff_combined_orbit_eventually_bounded :
    RiemannHypothesis ↔
      ∃ T C : ℝ, ∀ d : ℝ, T ≤ d →
        ‖combinedArithmeticOrbitV1 detectingPacket d‖ ≤ C := by
  obtain ⟨Td, hDictionary⟩ := eventual_signed_prime_equals_combined_v8
  constructor
  · intro hRH
    obtain ⟨Tb, C, hBound⟩ := fixed_signed_prime_eventually_bounded_iff_rh.mpr hRH
    refine ⟨max Td Tb, C, ?_⟩
    intro d hd
    rw [← hDictionary d ((le_max_left Td Tb).trans hd)]
    exact hBound d ((le_max_right Td Tb).trans hd)
  · rintro ⟨Tb, C, hBound⟩
    apply fixed_signed_prime_eventually_bounded_iff_rh.mp
    refine ⟨max Td Tb, C, ?_⟩
    intro d hd
    rw [hDictionary d ((le_max_left Td Tb).trans hd)]
    exact hBound d ((le_max_right Td Tb).trans hd)

/-- Higher prime powers change the genuine arithmetic convolution by a
uniformly bounded term on nonnegative shifts. Thus the *prime-only* orbit has
the same eventual-boundedness criterion, without importing an assumption about
its growth. This is an iff, not a bound established unconditionally. -/
theorem rh_iff_prime_only_orbit_eventually_bounded :
    RiemannHypothesis ↔
      ∃ T C : ℝ, ∀ d : ℝ, T ≤ d →
        ‖primeOnlyOrbitV1 detectingPacket d‖ ≤ C := by
  obtain ⟨D, _hD0, hD⟩ :=
    combinedArithmetic_boundedDifference_primeOnly_v1 detectingPacket
  constructor
  · intro hRH
    obtain ⟨T, C, hBound⟩ :=
      rh_iff_combined_orbit_eventually_bounded.mp hRH
    refine ⟨max T 0, C + D, ?_⟩
    intro d hd
    have hT : T ≤ d := (le_max_left T 0).trans hd
    have h0 : 0 ≤ d := (le_max_right T 0).trans hd
    calc
      ‖primeOnlyOrbitV1 detectingPacket d‖ =
          ‖(primeOnlyOrbitV1 detectingPacket d -
             combinedArithmeticOrbitV1 detectingPacket d) +
             combinedArithmeticOrbitV1 detectingPacket d‖ := by
               congr 1
               ring
      _ ≤ ‖primeOnlyOrbitV1 detectingPacket d -
             combinedArithmeticOrbitV1 detectingPacket d‖ +
            ‖combinedArithmeticOrbitV1 detectingPacket d‖ := norm_add_le _ _
      _ = ‖combinedArithmeticOrbitV1 detectingPacket d -
             primeOnlyOrbitV1 detectingPacket d‖ +
            ‖combinedArithmeticOrbitV1 detectingPacket d‖ := by
              rw [norm_sub_rev]
      _ ≤ D + C := add_le_add (hD d h0) (hBound d hT)
      _ = C + D := by ring
  · intro hPrime
    obtain ⟨T, C, hBound⟩ := hPrime
    apply rh_iff_combined_orbit_eventually_bounded.mpr
    refine ⟨max T 0, C + D, ?_⟩
    intro d hd
    have hT : T ≤ d := (le_max_left T 0).trans hd
    have h0 : 0 ≤ d := (le_max_right T 0).trans hd
    calc
      ‖combinedArithmeticOrbitV1 detectingPacket d‖ =
          ‖(combinedArithmeticOrbitV1 detectingPacket d -
             primeOnlyOrbitV1 detectingPacket d) +
             primeOnlyOrbitV1 detectingPacket d‖ := by
               congr 1
               ring
      _ ≤ ‖combinedArithmeticOrbitV1 detectingPacket d -
             primeOnlyOrbitV1 detectingPacket d‖ +
            ‖primeOnlyOrbitV1 detectingPacket d‖ := norm_add_le _ _
      _ ≤ D + C := add_le_add (hD d h0) (hBound d hT)
      _ = C + D := by ring

/-- Exact cofinal positive-pi-window RH criterion. The finite-to-cofinal
window theorem is reused directly from PR7; no upward monotonicity is assumed. -/
theorem rh_iff_pi_nat_windows :
    RiemannHypothesis ↔
      ∀ n : ℕ, 0 < n →
        AEGIS.WeilWindowExhaustionV1.WindowArithmeticNonpositiveV1
          ((n : ℝ) * Real.pi) := by
  have hAll :
      RiemannHypothesis ↔
        ∀ L : ℝ, 0 < L →
          AEGIS.WeilWindowExhaustionV1.WindowArithmeticNonpositiveV1 L :=
    AEGIS.WeilRHImpliesFinalSignV13.rh_iff_final_sign_v13.trans
      (AEGIS.RHFinalClosureV1.final_sign_residual_iff_weil_negativity_v1.trans
        AEGIS.WeilWindowExhaustionV1.weil_compact_smooth_negativity_iff_all_windows_v1)
  exact hAll.trans
    (FormalConjecturesUtil.FixedWindowLimitBridge.all_positive_windows_iff_pi_nat_windows
      AEGIS.WeilWindowExhaustionV1.WindowArithmeticNonpositiveV1
      (fun {R₁ R₂} hR hWin =>
        AEGIS.WeilWindowExhaustionV1.windowArithmeticNonpositive_mono_v1 hR hWin))

/-- The genuine Feshbach/Schur lower bound composed with PR7's cofinal
N^(-4) limit bridge. This closes the *abstract limit passage* once a cofinal
family of actual certified Schur inequalities and convergence is supplied. -/
theorem cofinal_feshbach_schur_limit_nonnegative
    {N : ℕ → ℕ}
    {a re_b q nv nw β c μ normSq : ℕ → ℝ}
    {Q normSqLimit : ℝ}
    (hN : Tendsto N atTop atTop)
    (hqLim : Tendsto
      (fun j => a j + 2 * re_b j + q j -
        μ j * (nv j ^ 2 + nw j ^ 2)) atTop (𝓝 Q))
    (hnormLim : Tendsto normSq atTop (𝓝 normSqLimit))
    (hnw : ∀ j, 0 ≤ nw j)
    (hq : ∀ j, c j * nw j ^ 2 ≤ q j)
    (hb : ∀ j, re_b j ^ 2 ≤ β j * nw j ^ 2)
    (hβ : ∀ j, 0 ≤ β j)
    (hμ : ∀ j, μ j < c j)
    (hSchur : ∀ j,
      -(FormalConjecturesUtil.FixedWindowLimitBridge.invFourthError 0 (N j)) *
        normSq j ≤
      a j - μ j * nv j ^ 2 - β j / (c j - μ j)) :
    0 ≤ Q := by
  apply FormalConjecturesUtil.FixedWindowLimitBridge.nonneg_of_cofinal_invFourth_fixed_window_lower_bound
    hN hqLim hnormLim
  intro j
  exact (hSchur j).trans
    (AEGIS.RHFeshbachCoreV1.feshbach_lower
      (a j) (re_b j) (q j) (nv j) (nw j) (β j) (c j) (μ j)
      (hnw j) (hq j) (hb j) (hβ j) (hμ j))

/-- Preserve both unconditional mathematical outputs across the formerly
separate tilt/complementarity and Abel/Chebyshev source subtrees. -/
theorem complementary_packets_and_signed_dictionary :
    (∃ p q : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧ WeilMomentConditionsV1 q ∧
      ∀ z : ℂ, 0 < z.re → z.re < 1 →
        ¬ (mellin p.1 z = 0 ∧ mellin q.1 z = 0)) ∧
      EventuallySignedPrimeEqualsCombinedOrbitV5 :=
  ⟨AEGIS.RHWeilTiltComplementarityV1.unconditional_moment_zero_complementary_pair,
   eventual_signed_prime_equals_combined_v8⟩

end AEGIS.RHExistingProofFusionV1

#print axioms AEGIS.RHExistingProofFusionV1.signed_dictionary_and_reflected_tail
#print axioms AEGIS.RHExistingProofFusionV1.rh_iff_combined_orbit_eventually_bounded
#print axioms AEGIS.RHExistingProofFusionV1.rh_iff_prime_only_orbit_eventually_bounded
#print axioms AEGIS.RHExistingProofFusionV1.rh_iff_pi_nat_windows
#print axioms AEGIS.RHExistingProofFusionV1.cofinal_feshbach_schur_limit_nonnegative
#print axioms AEGIS.RHExistingProofFusionV1.complementary_packets_and_signed_dictionary
