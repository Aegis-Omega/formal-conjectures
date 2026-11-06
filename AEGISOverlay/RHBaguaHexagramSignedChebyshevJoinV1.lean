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

import AEGISOverlay.RHSignedPrimeIntervalExtensionV8
import AEGISOverlay.RHBaguaActualWeilV1
import AEGISOverlay.RHOptimizedSchurGlobalJoinV1

/-!
# Actual Weil Bagua/Hexagram signed Chebyshev integration

One shared *actual* WeilCompactSmoothGV1 packet is used in each equality.
For arbitrary complex mode amplitudes, the original Weil B pairing retains
all 8x8 or 64x64 mixed coefficients; the same packet simultaneously has
the full signed Chebyshev psi-discrepancy representation at late shifts.

No XOR-circulant hypothesis, independent artificial Gram, absolute-value
prime domination, cofinal reconstruction or universal Weil sign is asserted.
In particular, the mixed-defect inequality remains an explicit obligation.

This source needs exact-head Lean compilation and axioms replay.
-/

open Set MeasureTheory Complex
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHBaguaHexagramSignedChebyshevJoinV1

open AEGIS.RHGramExpansionV13
open AEGIS.RHActualNarrowGramSignV1
open AEGIS.RHBaguaActualWeilV1
open AEGIS.RHOptimizedSchurGlobalJoinV1
open AEGIS.RHSignedPrimeIntervalExtensionV8
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilSignedKernelReductionV1
open AEGIS.RHPrimeOnlyGrowthBridgeV1

/-- Every complex-weighted Bagua superposition keeps both zero moments. -/
theorem bagua_weighted_packet_moments
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (z : Fin 8 → ℂ) :
    WeilMomentConditionsV1 (packetSum z (baguaMode gs)) := by
  apply trigram_moment_packetSum 7 z (baguaMode gs)
  intro a
  exact bagua_mode_moments gs hm a

/-- Bagua H8: the same genuine packet has the complete actual Weil Gram
(including all complex cross terms) and the signed Chebyshev representation.
Neither identity on its own asserts the Weil sign. -/
theorem bagua_actual_weil_and_signed_chebyshev
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (z : Fin 8 → ℂ) :
    (B (packetSum z (baguaMode gs)) (packetSum z (baguaMode gs)) =
      ∑ a : Fin 8, ∑ b : Fin 8,
        z a * star (z b) * baguaActualGram gs a b) ∧
    (∃ T : ℝ, ∀ d : ℝ, T ≤ d →
      SignedPrimeCorrelationV1 (packetSum z (baguaMode gs)) d =
        ∫ x in Ioi (0 : ℝ),
          primeDiscrepancyKernelV1
            (packetSum z (baguaMode gs)) (d - Real.log x) *
            (((Real.exp (-Real.log x / 2) *
                (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ))) := by
  constructor
  · exact bagua_actual_weighted_gram_exact gs z
  · exact signed_prime_eq_full_chebyshev_for_packet_v8
      (packetSum z (baguaMode gs)) (bagua_weighted_packet_moments gs hm z)

/-- Every complex-weighted H64 mode family is still moment zero. -/
theorem hexagram64_weighted_packet_moments
    (gs : Fin 64 → WeilCompactSmoothGV1)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (z : Fin 64 → ℂ) :
    WeilMomentConditionsV1 (packetSum z (hexagram64WalshMode gs)) := by
  apply trigram_moment_packetSum 63 z (hexagram64WalshMode gs)
  intro a
  exact hexagram64WalshMode_moments gs hm a

/-- Hexagram H64: exact actual 4096-entry Weil pairing together with
the same arbitrary-mode packet's signed Chebyshev representation.
It uses the tensor 8x8 Walsh structure from the existing source. -/
theorem hexagram64_actual_weil_and_signed_chebyshev
    (gs : Fin 64 → WeilCompactSmoothGV1)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (z : Fin 64 → ℂ) :
    (B (packetSum z (hexagram64WalshMode gs))
        (packetSum z (hexagram64WalshMode gs)) =
      ∑ a : Fin 64, ∑ b : Fin 64,
        z a * star (z b) * hexagram64WalshGram gs a b) ∧
    (∃ T : ℝ, ∀ d : ℝ, T ≤ d →
      SignedPrimeCorrelationV1
        (packetSum z (hexagram64WalshMode gs)) d =
        ∫ x in Ioi (0 : ℝ),
          primeDiscrepancyKernelV1
            (packetSum z (hexagram64WalshMode gs)) (d - Real.log x) *
            (((Real.exp (-Real.log x / 2) *
                (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ))) := by
  constructor
  · exact hexagram64WalshGram_weighted_exact gs z
  · exact signed_prime_eq_full_chebyshev_for_packet_v8
      (packetSum z (hexagram64WalshMode gs))
      (hexagram64_weighted_packet_moments gs hm z)

/-- The *actual* missing H64 cross-channel signed budget is exactly the
existing mixed-defect criterion; no positivity is smuggled into the join. -/
theorem hexagram64_actual_signed_defect_iff_weil_nonpositive
    (gs : Fin 64 → WeilCompactSmoothGV1) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect
        63 (hexagram64WalshMode gs) ≤
      -(∑ i : Fin 64,
          (B (hexagram64WalshMode gs i)
            (hexagram64WalshMode gs i)).re) ↔
    (B (packetSum (fun _ => (1 : ℂ)) (hexagram64WalshMode gs))
       (packetSum (fun _ => (1 : ℂ)) (hexagram64WalshMode gs))).re ≤ 0 := by
  exact actual_signed_defect_iff_packet_nonpositive
    (hexagram64WalshMode gs)

end AEGIS.RHBaguaHexagramSignedChebyshevJoinV1

#print axioms AEGIS.RHBaguaHexagramSignedChebyshevJoinV1.bagua_weighted_packet_moments
#print axioms AEGIS.RHBaguaHexagramSignedChebyshevJoinV1.bagua_actual_weil_and_signed_chebyshev
#print axioms AEGIS.RHBaguaHexagramSignedChebyshevJoinV1.hexagram64_weighted_packet_moments
#print axioms AEGIS.RHBaguaHexagramSignedChebyshevJoinV1.hexagram64_actual_weil_and_signed_chebyshev
#print axioms AEGIS.RHBaguaHexagramSignedChebyshevJoinV1.hexagram64_actual_signed_defect_iff_weil_nonpositive
