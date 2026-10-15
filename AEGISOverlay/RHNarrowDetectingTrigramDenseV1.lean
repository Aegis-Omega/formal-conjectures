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
import AEGISOverlay.RHFixedPacketDenseShiftV1

/-!
# Fixed detecting packet: stronger Trigram interval and exact dense-shift RH bridge

The fixed moment-zero packet in RHNarrowFixedDetectorV1 has log support in
[-1/32, 1/32] and detects EVERY nontrivial zeta zero. A two-point translate
g + c T_d g fits into a COMMON Trigram window of radius 2/5, centered at d/2,
whenever |d| <= 59/80, because 1/32 + (59/80)/2 = 2/5.

This strengthens the already-certified local interval |d| <= 3/16, without
changing the detector. For the same packet, dense four-phase arithmetic signs
on Z log 2 + Z log 3 are equivalent to RiemannHypothesis. The present local
interval theorem does NOT imply the dense-group sign for all shifts. The
unproved global continuation is kept as an explicit proposition.
-/

open Set Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNarrowDetectingTrigramDenseV1

open AEGIS.RHNarrowFixedDetectorV1
open AEGIS.RestrictedWeilCriterionResidueWitnessV11
open AEGIS.RestrictedWeilCriterionResidueCoefficientV11
open AEGIS.RHTargetPacketMellinGeneralV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.RestrictedWeilCriterionKernelBridgeV10
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroTranslationV11

/-- Geometric identity of the two local radii, entirely rational. -/
theorem exact_trigram_shift_radius :
    (1 / 32 : ℝ) + (59 / 80 : ℝ) / 2 = 2 / 5 := by
  norm_num

/-- A two-point translate of the *fixed detecting packet* remains within
one radius-2/5 common log window for |d| <= 59/80, at midpoint d/2. -/
theorem narrow_detector_trigram_two_point_window
    (d : ℝ) (hd : |d| ≤ (59 / 80 : ℝ)) (c : ℂ) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c)
      (2 / 5 : ℝ) (d / 2) := by
  let g := narrowDetectingPacket
  have hdlo := (abs_le.mp hd).1
  have hdhi := (abs_le.mp hd).2
  have hg : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      g (-(1 / 32 : ℝ)) (1 / 32 : ℝ) :=
    narrowDetectingPacket_logWindow
  have hleft : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      g (d / 2 - (2 / 5 : ℝ)) (d / 2 + (2 / 5 : ℝ)) := by
    intro t ht
    have h := hg ht
    exact ⟨by linarith [h.1, hdhi], by linarith [h.2, hdlo]⟩
  have htrans := AEGIS.WeilThreeBlockTranslatedPacketsV22.translate_logSupportIn
    g d (-(1 / 32 : ℝ)) (1 / 32 : ℝ) hg
  have hright : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d)
      (d / 2 - (2 / 5 : ℝ)) (d / 2 + (2 / 5 : ℝ)) := by
    intro t ht
    have h := htrans ht
    exact ⟨by linarith [h.1, hdlo], by linarith [h.2, hdhi]⟩
  change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
    (WeilTwoPointTranslateV11 g d c)
    (d / 2 - (2 / 5 : ℝ)) (d / 2 + (2 / 5 : ℝ))
  unfold AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
  apply closure_minimal ?_ isClosed_Icc
  intro t ht
  by_contra houtside
  have hfirst : AEGIS.WeilLogCoordinateIsometryV21.logLift g.1 t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => houtside (hleft hs))
  have hsecond :
      AEGIS.WeilLogCoordinateIsometryV21.logLift
        (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1 t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => houtside (hright hs))
  have heq : AEGIS.WeilLogCoordinateIsometryV21.logLift
      (WeilTwoPointTranslateV11 g d c).1 t =
      AEGIS.WeilLogCoordinateIsometryV21.logLift g.1 t +
      c * AEGIS.WeilLogCoordinateIsometryV21.logLift
        (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1 t := by
    change ((Real.exp (t / 2) : ℂ) *
        (g.1 (Real.exp t) +
          c * (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1
            (Real.exp t))) =
      ((Real.exp (t / 2) : ℂ) * g.1 (Real.exp t)) +
        c * ((Real.exp (t / 2) : ℂ) *
          (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d).1
            (Real.exp t))
    ring
  apply ht
  rw [heq, hfirst, hsecond]
  ring

/-- Genuine Weil arithmetic sign, not a proxy, for every complex c and
all translations in the exact larger interval. Both moments vanish. -/
theorem narrow_detector_trigram_two_point_sign
    (d : ℝ) (hd : |d| ≤ (59 / 80 : ℝ)) (c : ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1
        (WeilTwoPointTranslateV11 narrowDetectingPacket d c))).re ≤ 0 := by
  have hm := AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
    narrowDetectingPacket d c narrowDetectingPacket_moments
  exact AEGIS.RHActualNarrowGramSignV1.trigram_actual_arithmetic_nonpositive_at
    (WeilTwoPointTranslateV11 narrowDetectingPacket d c) (d / 2)
    hm (narrow_detector_trigram_two_point_window d hd c)

/-- Four-phase signs for one fixed detecting packet at every point
of the dense logarithmic group. No spurious global sign is asserted. -/
def DenseNarrowDetectorFourPhaseSign : Prop :=
  AEGIS.RHFixedPacketDenseShiftV1.DensePacketFourPhaseSignV1 narrowDetectingPacket

theorem riemannHypothesis_of_dense_narrow_detector
    (h : DenseNarrowDetectorFourPhaseSign) : RiemannHypothesis :=
  AEGIS.RHNarrowFixedDetectorV1.riemannHypothesis_of_narrow_four_phase_sign
    (AEGIS.RHFixedPacketDenseShiftV1.dense_packet_four_phase_implies_all_shifts
      narrowDetectingPacket narrowDetectingPacket_moments h)

theorem dense_narrow_detector_of_riemannHypothesis
    (h : RiemannHypothesis) : DenseNarrowDetectorFourPhaseSign := by
  intro d _hd c _hc
  have hm :=
    AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
      narrowDetectingPacket d c narrowDetectingPacket_moments
  exact (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c) hm).mpr
    (AEGIS.WeilRHImpliesFinalSignV13.rh_implies_universal_v13
      h (WeilTwoPointTranslateV11 narrowDetectingPacket d c) hm)

/-- Reduction to one fixed detecting packet and a dense four-phase shift test.
The right-to-left arrow is fully formal. This is an EQUIVALENCE, not a
proof of the global dense sign. -/
theorem dense_narrow_detector_iff_riemannHypothesis :
    DenseNarrowDetectorFourPhaseSign ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_dense_narrow_detector,
    dense_narrow_detector_of_riemannHypothesis⟩

end AEGIS.RHNarrowDetectingTrigramDenseV1

#print axioms AEGIS.RHNarrowDetectingTrigramDenseV1.exact_trigram_shift_radius
#print axioms AEGIS.RHNarrowDetectingTrigramDenseV1.narrow_detector_trigram_two_point_window
#print axioms AEGIS.RHNarrowDetectingTrigramDenseV1.narrow_detector_trigram_two_point_sign
#print axioms AEGIS.RHNarrowDetectingTrigramDenseV1.riemannHypothesis_of_dense_narrow_detector
#print axioms AEGIS.RHNarrowDetectingTrigramDenseV1.dense_narrow_detector_of_riemannHypothesis
#print axioms AEGIS.RHNarrowDetectingTrigramDenseV1.dense_narrow_detector_iff_riemannHypothesis
