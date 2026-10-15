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

import AEGISOverlay.RHNarrowDetectingTrigramDenseV1
import RHKreinL105AllV1

open Set Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNarrowDetectingL105V1

open AEGIS.RHNarrowFixedDetectorV1
open AEGIS.RestrictedWeilCriterionResidueWitnessV11
open AEGIS.RestrictedWeilCriterionResidueCoefficientV11
open AEGIS.RHTargetPacketMellinGeneralV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.RestrictedWeilCriterionKernelBridgeV10
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroTranslationV11

/-! ## Source-pinned width 21/20 Krein upgrade

The independent 116-batch L105 certificate is stronger than the earlier
2/5 Trigram window in the two-point DETECTING packet geometry. It is
valid at arbitrary log-window centers. We preserve that center d/2,
rather than incorrectly using the window criterion centered at zero.

This gives a genuinely wider STRICT radius |d| < 79/80, exactly since
2 * (1/32 + |d|/2) < 21/20 iff |d| < 79/80. No global dense-shift sign
is inferred. The original narrower 59/80 theorem is retained unchanged.
-/

/-- The detecting two-point packet fits into its smallest natural
logarithmic midpoint window, for ANY real shift. -/
theorem narrow_detector_two_point_window_of_radius
    (d : ℝ) (c : ℂ) (radius : ℝ)
    (hr : (1 / 32 : ℝ) + |d| / 2 ≤ radius) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c)
      radius (d / 2) := by
  let g := narrowDetectingPacket
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp (le_refl (|d|))
  have hg : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      g (-(1 / 32 : ℝ)) (1 / 32 : ℝ) :=
    narrowDetectingPacket_logWindow
  have hleft : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      g (d / 2 - radius) (d / 2 + radius) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := hg ht
    exact ⟨by linarith, by linarith⟩
  have htrans := AEGIS.WeilThreeBlockTranslatedPacketsV22.translate_logSupportIn
    g d (-(1 / 32 : ℝ)) (1 / 32 : ℝ) hg
  have hright : AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
      (AEGIS.WeilThreeBlockTranslatedPacketsV22.translatePacket g d)
      (d / 2 - radius) (d / 2 + radius) := by
    intro t ht
    obtain ⟨hlo, hhi⟩ := htrans ht
    exact ⟨by linarith, by linarith⟩
  change AEGIS.WeilThreeBlockTranslatedPacketsV22.LogSupportIn
    (WeilTwoPointTranslateV11 g d c)
    (d / 2 - radius) (d / 2 + radius)
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

/-- ACTUAL moment-zero Weil sign on the wider |d| < 79/80 detector
interval, for EVERY complex phase. The sole analytic input is the
existing unconditional L105 finite+tail Krein kernel certificate.
This does not assume RH, nor any all-shifts four-phase sign. -/
theorem narrow_detector_L105_two_point_sign
    (d : ℝ) (hd : |d| < (79 / 80 : ℝ)) (c : ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1
        (WeilTwoPointTranslateV11 narrowDetectingPacket d c))).re ≤ 0 := by
  let radius : ℝ := (1 / 32 : ℝ) + |d| / 2
  have hpos : 0 ≤ radius := by
    dsimp [radius]
    positivity
  have hcert : 2 * radius < (21 / 20 : ℝ) := by
    dsimp [radius]
    linarith
  have hm := AEGIS.WeilZeroKernelHermitianV11.twoPointTranslate_preserves_moments_v11
    narrowDetectingPacket d c narrowDetectingPacket_moments
  have hw := narrow_detector_two_point_window_of_radius d c radius (le_refl _)
  have hzero := AEGIS.RHKreinL105AllV1.zero_quadratic_nonneg_width_21_20
    (WeilTwoPointTranslateV11 narrowDetectingPacket d c)
    hm radius (d / 2) hpos hcert hw
  exact
    (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (WeilTwoPointTranslateV11 narrowDetectingPacket d c) hm).mpr hzero


end AEGIS.RHNarrowDetectingL105V1

#print axioms AEGIS.RHNarrowDetectingL105V1.narrow_detector_two_point_window_of_radius
#print axioms AEGIS.RHNarrowDetectingL105V1.narrow_detector_L105_two_point_sign
