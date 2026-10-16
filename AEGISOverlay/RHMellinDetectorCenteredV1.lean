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

import AEGISOverlay.RHNarrowFixedDetectorV1
import AEGISOverlay.RHActualNarrowGramSignV1
import AEGISOverlay.RHOptimizedSchurGlobalJoinV1

/-!
# Centered Mellin detector: exact 59/80 local Weil sign and H64 transport

The fixed detecting packet has log support in [-1/32,1/32].
Center its two-point translates at d/2. The actual 2/5 Trigram
coercivity theorem then applies whenever |d| <= 59/80, with all
genuine prime, Archimedean, and off-diagonal Weil contributions.

For 64 translates sharing a center with radius 59/160, the source
Walsh-Weil Gram theorem preserves all 4096 entries and its 1/16 margin.
No all-shift estimate or unconditional RiemannHypothesis is asserted.
-/

open Set Complex
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHMellinDetectorCenteredV1

open AEGIS.RHNarrowFixedDetectorV1
open AEGIS.RHActualNarrowGramSignV1
open AEGIS.WeilZeroTwoPointV11
open AEGIS.RestrictedWeilCriterionKernelBridgeV10

theorem midpoint_twoPoint_window
    (d : ℝ) (hd : |d| ≤ (59 / 80 : ℝ)) (c : ℂ) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c)
      (2 / 5 : ℝ) (d / 2) := by
  let g := narrowDetectingPacket
  have hdlo : -(59 / 80 : ℝ) ≤ d := (abs_le.mp hd).1
  have hdhi : d ≤ (59 / 80 : ℝ) := (abs_le.mp hd).2
  have hg : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      g (-(1 / 32 : ℝ)) (1 / 32 : ℝ) :=
    narrowDetectingPacket_logWindow
  have hleft : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      g (d / 2 - 2 / 5) (d / 2 + 2 / 5) := by
    intro t ht
    have h := hg ht
    constructor <;> linarith [h.1, h.2, hdlo, hdhi]
  have htrans := AEGIS.WeilThreeBlockTranslatedPacketsV22.translate_logSupportIn
    g d (-(1 / 32 : ℝ)) (1 / 32 : ℝ) hg
  have hright : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d)
      (d / 2 - 2 / 5) (d / 2 + 2 / 5) := by
    intro t ht
    have h := htrans ht
    constructor <;> linarith [h.1, h.2, hdlo, hdhi]
  change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
    (WeilTwoPointTranslateV11 g d c) (d / 2 - 2 / 5) (d / 2 + 2 / 5)
  unfold AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
  apply closure_minimal ?_ isClosed_Icc
  intro t ht
  by_contra houtside
  have hfirst : AEGIS.WeilLogCoordinateIsometryV21.logLift g.1 t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => houtside (hleft hs))
  have hsecond : AEGIS.WeilLogCoordinateIsometryV21.logLift
      (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1 t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => houtside (hright hs))
  have heq :
      AEGIS.WeilLogCoordinateIsometryV21.logLift
        (WeilTwoPointTranslateV11 g d c).1 t =
      AEGIS.WeilLogCoordinateIsometryV21.logLift g.1 t +
        c * AEGIS.WeilLogCoordinateIsometryV21.logLift
          (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1 t := by
    change ((Real.exp (t / 2) : ℂ) *
        (g.1 (Real.exp t) +
          c * (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1
            (Real.exp t))) =
      ((Real.exp (t / 2) : ℂ) * g.1 (Real.exp t) +
        c * ((Real.exp (t / 2) : ℂ) *
          (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1
            (Real.exp t))
    ring
  apply ht
  rw [heq, hfirst, hsecond]
  ring

theorem midpoint_twoPoint_actual_margin
    (d : ℝ) (hd : |d| ≤ (59 / 80 : ℝ)) (c : ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1
        (WeilTwoPointTranslateV11 narrowDetectingPacket d c))).re ≤
      -(1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy
        (WeilTwoPointTranslateV11 narrowDetectingPacket d c).1 := by
  have hm := AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
    narrowDetectingPacket d c narrowDetectingPacket_moments
  exact trigram_actual_arithmetic_margin_at
    (WeilTwoPointTranslateV11 narrowDetectingPacket d c)
    (d / 2) hm (midpoint_twoPoint_window d hd c)

theorem midpoint_twoPoint_actual_nonpositive
    (d : ℝ) (hd : |d| ≤ (59 / 80 : ℝ)) (c : ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1
        (WeilTwoPointTranslateV11 narrowDetectingPacket d c))).re ≤ 0 := by
  have h := midpoint_twoPoint_actual_margin d hd c
  have he := AEGIS.WeilDisjointEnergyV2.energy_nonnegative
    (WeilTwoPointTranslateV11 narrowDetectingPacket d c).1
  linarith

theorem midpoint_twoPoint_zero_nonnegative
    (d : ℝ) (hd : |d| ≤ (59 / 80 : ℝ)) (c : ℂ) :
    0 ≤ (AEGIS.WeilZeroTranslationV11.WeilAutocorrelationZeroQuadraticV11
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c)).re := by
  have hm := AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
    narrowDetectingPacket d c narrowDetectingPacket_moments
  exact
    (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c) hm).mp
        (midpoint_twoPoint_actual_nonpositive d hd c)

theorem midpoint_twoPoint_kernel_norm_bound
    (d : ℝ) (hd : |d| ≤ (59 / 80 : ℝ)) :
    ‖AEGIS.WeilZeroTwoPointV11.WeilZeroTranslationKernelV11
        narrowDetectingPacket d‖ ≤
      2 * (AEGIS.WeilZeroTranslationV11.WeilAutocorrelationZeroQuadraticV11
        narrowDetectingPacket).re := by
  apply weil_four_phase_nonnegative_norm_bound_v1
  intro c _hc
  rw [← AEGIS.RHFixedPacketFourPhaseV1.twoPoint_zero_quadratic_re_eq_four_phase_value
    narrowDetectingPacket narrowDetectingPacket_moments d c]
  exact midpoint_twoPoint_zero_nonnegative d hd c

theorem narrow_translate_centered_window
    (d center : ℝ) (hd : |d - center| ≤ (59 / 160 : ℝ)) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket
        narrowDetectingPacket d) (2 / 5 : ℝ) center := by
  have hg : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      narrowDetectingPacket (-(1 / 32 : ℝ)) (1 / 32 : ℝ) :=
    narrowDetectingPacket_logWindow
  have ht := AEGIS.WeilThreeBlockTranslatedPacketsV22.translate_logSupportIn
    narrowDetectingPacket d (-(1 / 32 : ℝ)) (1 / 32 : ℝ) hg
  change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
    (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket
      narrowDetectingPacket d) (center - 2 / 5) (center + 2 / 5)
  intro t htmem
  have h := ht htmem
  obtain ⟨hlo, hhi⟩ := abs_le.mp hd
  constructor <;> linarith [h.1, h.2, hlo, hhi]

theorem narrow_hexagram64_full_actual_margin
    (shifts : Fin 64 → ℝ) (center : ℝ)
    (hspan : ∀ i, |shifts i - center| ≤ (59 / 160 : ℝ))
    (z : Fin 64 → ℂ) :
    (1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy
      (AEGIS.RHGramExpansionV13.packetSum z
        (AEGIS.RHOptimizedSchurGlobalJoinV1.hexagram64WalshMode
          (fun i : Fin 64 =>
            AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket
              narrowDetectingPacket (shifts i)))).1 ≤
    -(∑ a : Fin 64, ∑ b : Fin 64,
        z a * star (z b) *
          AEGIS.RHOptimizedSchurGlobalJoinV1.hexagram64WalshGram
            (fun i : Fin 64 =>
              AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket
                narrowDetectingPacket (shifts i)) a b).re := by
  let gs : Fin 64 → WeilCompactSmoothGV1 := fun i =>
    AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket
      narrowDetectingPacket (shifts i)
  have hm : ∀ i, WeilMomentConditionsV1 (gs i) := by
    intro i
    exact AEGIS.WeilThreeBlockTranslatedPacketsV22.translate_preserves_moments
      narrowDetectingPacket (shifts i) narrowDetectingPacket_moments
  have hw : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (2 / 5) center := by
    intro i
    exact narrow_translate_centered_window (shifts i) center (hspan i)
  exact AEGIS.RHOptimizedSchurGlobalJoinV1.hexagram64Walsh_full_weighted_margin
    gs center hm hw z

theorem narrow_hexagram64_fs_mellin
    (p : ℝ) (ticks : Fin 64 → ℤ) (i : Fin 64) (s : ℂ) :
    mellin (AEGIS.RHTimeSliceWeilV1.timeSliceFamily
      narrowDetectingPacket p ticks i).1 s =
      Complex.exp ((s - (1 / 2 : ℂ)) *
        (AEGIS.RHTimeSliceWeilV1.fsLogSlice p (ticks i) : ℂ)) *
        mellin narrowDetectingPacket.1 s := by
  exact AEGIS.RHTimeSliceWeilV1.timeSlice_mellin
    narrowDetectingPacket s p (ticks i)

end AEGIS.RHMellinDetectorCenteredV1

#print axioms AEGIS.RHMellinDetectorCenteredV1.midpoint_twoPoint_actual_margin
#print axioms AEGIS.RHMellinDetectorCenteredV1.midpoint_twoPoint_kernel_norm_bound
#print axioms AEGIS.RHMellinDetectorCenteredV1.narrow_hexagram64_full_actual_margin
#print axioms AEGIS.RHMellinDetectorCenteredV1.narrow_hexagram64_fs_mellin
