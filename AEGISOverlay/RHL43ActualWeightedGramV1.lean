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

import AEGISOverlay.RHActualNarrowGramSignV1
import CvSWindowL43V1

/-!
# Genuine full weighted Weil Gram on the unconditional CvS L=4/3 window

Reuses the existing zero-side positivity at logarithmic half-width <= 2/3
and the genuine complex Hermitian Gram expansion. Unlike the prior 2/5
Trigram theorem, the conclusion covers ALL mixed terms for arbitrary
complex coefficients on a common half-width-2/3 window.

This is a window theorem, not an unrestricted RH proof. No new axioms,
`sorry`, or approximation claims are introduced.
-/

open Set
open scoped ContDiff BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHL43ActualWeightedGramV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.RHKreinFactorV13
open AEGIS.RHGramExpansionV13
open AEGIS.RHDyadicDiagonalV13

/-- Multiplying an actual Weil packet by a complex scalar cannot enlarge
its logarithmic support. The radius is arbitrary. -/
theorem halfWidth_scale (u : WeilCompactSmoothGV1) (z : ℂ) (a r : ℝ)
    (hu : HalfWidthAt u r a) : HalfWidthAt (scalePacket z u) r a := by
  change tsupport (lift (scalePacket z u).1) ⊆ Icc (a - r) (a + r)
  change tsupport (lift u.1) ⊆ Icc (a - r) (a + r) at hu
  have hlift : lift (scalePacket z u).1 =
      (fun x => z * lift u.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, scalePacket]
    ring
  rw [hlift]
  have hs : tsupport (fun x => z * lift u.1 x) ⊆ tsupport (lift u.1) := by
    apply closure_minimal ?_ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    have hz : lift u.1 x = 0 := image_eq_zero_of_notMem_tsupport hn
    exact hx (by simp [hz])
  exact hs.trans hu

/-- Adding actual Weil packets in a common window retains that window,
for any nonnegative radius (the proof needs no radius inequality). -/
theorem halfWidth_add (u v : WeilCompactSmoothGV1) (a r : ℝ)
    (hu : HalfWidthAt u r a) (hv : HalfWidthAt v r a) :
    HalfWidthAt (addPacket u v) r a := by
  change tsupport (lift (addPacket u v).1) ⊆ Icc (a - r) (a + r)
  change tsupport (lift u.1) ⊆ Icc (a - r) (a + r) at hu
  change tsupport (lift v.1) ⊆ Icc (a - r) (a + r) at hv
  have hlift : lift (addPacket u v).1 =
      (fun x => lift u.1 x + lift v.1 x) := by
    funext x
    simp only [AEGIS.RHKreinFactorV13.lift, addPacket, mul_add]
  rw [hlift]
  have hs :
      tsupport (fun x => lift u.1 x + lift v.1 x) ⊆
        tsupport (lift u.1) ∪ tsupport (lift v.1) := by
    apply closure_minimal ?_
      ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro x hx
    by_contra hn
    have hu0 : lift u.1 x = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hxU
      exact hn (Or.inl hxU))
    have hv0 : lift v.1 x = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hxV
      exact hn (Or.inr hxV))
    exact hx (by simp [hu0, hv0])
  intro x hx
  rcases hs hx with hxU | hxV
  · exact hu hxU
  · exact hv hxV

/-- Arbitrarily many complex-weighted actual Weil packets in one common
logarithmic window remain in that window. No common mother assumption. -/
theorem halfWidth_packetSum :
    ∀ (n : ℕ) (z : Fin (n + 1) → ℂ)
      (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center r : ℝ),
      (∀ i, HalfWidthAt (gs i) r center) →
      HalfWidthAt (packetSum z gs) r center := by
  intro n
  induction n with
  | zero =>
      intro z gs center r hwin
      change HalfWidthAt (scalePacket (z 0) (gs 0)) r center
      exact halfWidth_scale (gs 0) (z 0) center r (hwin 0)
  | succ n ih =>
      intro z gs center r hwin
      change HalfWidthAt
        (addPacket
          (packetSum (fun i : Fin (n + 1) => z i.castSucc)
            (fun i : Fin (n + 1) => gs i.castSucc))
          (scalePacket (z (Fin.last (n + 1)))
            (gs (Fin.last (n + 1))))) r center
      exact halfWidth_add _ _ center r
        (ih (fun i => z i.castSucc) (fun i => gs i.castSucc)
          center r (fun i => hwin i.castSucc))
        (halfWidth_scale _ _ center r (hwin (Fin.last (n + 1))))

/-- New source-exact finite-dimensional coercivity SIGN for the COMPLETE
complex Hermitian Weil matrix in the existing L=4/3 window. The support
hypothesis is on every original genuine packet, not on a substitute matrix;
all off-diagonal coefficients are retained. -/
theorem l43_full_weighted_actual_gram_nonpositive
    (n : ℕ) (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (center : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, HalfWidthAt (gs i) (2 / 3) center) :
    (∑ i, ∑ j, z i * star (z j) * B (gs i) (gs j)).re ≤ 0 := by
  have hmSum := AEGIS.RHActualNarrowGramSignV1.trigram_moment_packetSum n z gs hm
  have hwSum := halfWidth_packetSum n z gs center (2 / 3) hwin
  have hzero := AEGIS.CvSWindowL43V1.window_L43
    (packetSum z gs) hmSum (2 / 3) center hwSum (by norm_num)
  have hsign :
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (packetSum z gs))).re ≤ 0 :=
    (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (packetSum z gs) hmSum).mpr hzero
  change (B (packetSum z gs) (packetSum z gs)).re ≤ 0 at hsign
  rw [AEGIS.RHGramExpansionV13.B_packetSum] at hsign
  exact hsign

/-! ## Genuine signed mixed-entry control over the larger L=4/3 window -/

/-- Two fine packets whose centers are at most 509/384 apart fit a common
half-width-2/3 logarithmic window. The constant is exact:
(1/256) + (509/384)/2 = 2/3. -/
theorem fine_width_into_l43_midpoint
    (u : WeilCompactSmoothGV1) (a b : ℝ)
    (hu : HalfWidthAt u (1 / 256) a)
    (hab : |a - b| ≤ (509 / 384 : ℝ)) :
    HalfWidthAt u (2 / 3) ((a + b) / 2) := by
  change tsupport (lift u.1) ⊆
    Icc ((a + b) / 2 - 2 / 3) ((a + b) / 2 + 2 / 3)
  change tsupport (lift u.1) ⊆
    Icc (a - 1 / 256) (a + 1 / 256) at hu
  intro t ht
  obtain ⟨hlo, hhi⟩ := hu ht
  obtain ⟨hablo, habhi⟩ := abs_le.mp hab
  constructor <;> linarith

/-- Signed TRUE mixed Weil interaction for any two differently shaped
moment-zero fine atoms with centers separated by ≤ 509/384. This extends
the existing Trigram near-pair cutoff 507/640 and retains the full
cross-term without a numerical Schur assumption. -/
theorem l43_fine_pair_signed_mixed_bound
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hmu : WeilMomentConditionsV1 u)
    (hmv : WeilMomentConditionsV1 v)
    (hu : HalfWidthAt u (1 / 256) a)
    (hv : HalfWidthAt v (1 / 256) b)
    (hab : |a - b| ≤ (509 / 384 : ℝ)) :
    2 * (B u v).re ≤ -(B u u).re - (B v v).re := by
  have hwa : HalfWidthAt u (2 / 3) ((a + b) / 2) :=
    fine_width_into_l43_midpoint u a b hu hab
  have hwb : HalfWidthAt v (2 / 3) ((a + b) / 2) := by
    have hba : |b - a| ≤ (509 / 384 : ℝ) := by
      simpa only [abs_sub_comm] using hab
    simpa only [add_comm] using
      fine_width_into_l43_midpoint v b a hv hba
  have hw : HalfWidthAt (addPacket u v) (2 / 3) ((a + b) / 2) :=
    halfWidth_add u v ((a + b) / 2) (2 / 3) hwa hwb
  have hm : WeilMomentConditionsV1 (addPacket u v) :=
    AEGIS.WeilFinalSignTranslationBoundV10.momentConditions_addPacket_v10 u v hmu hmv
  have hzero := AEGIS.CvSWindowL43V1.window_L43
    (addPacket u v) hm (2 / 3) ((a + b) / 2) hw (by norm_num)
  have hsign :
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (addPacket u v))).re ≤ 0 :=
    (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (addPacket u v) hm).mpr hzero
  change (B (addPacket u v) (addPacket u v)).re ≤ 0 at hsign
  have hgram :=
    AEGIS.RHCofinalSchurAdapterV1.actual_two_block_gram_coefficients u v
  linarith

end AEGIS.RHL43ActualWeightedGramV1

#print axioms AEGIS.RHL43ActualWeightedGramV1.halfWidth_scale
#print axioms AEGIS.RHL43ActualWeightedGramV1.halfWidth_add
#print axioms AEGIS.RHL43ActualWeightedGramV1.halfWidth_packetSum
#print axioms AEGIS.RHL43ActualWeightedGramV1.l43_full_weighted_actual_gram_nonpositive
#print axioms AEGIS.RHL43ActualWeightedGramV1.fine_width_into_l43_midpoint
#print axioms AEGIS.RHL43ActualWeightedGramV1.l43_fine_pair_signed_mixed_bound