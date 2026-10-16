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

import AEGISOverlay.RHScaleRowCompositionV1
import AEGISOverlay.RHTimeSliceWeilV1
import AEGISOverlay.RHLogThreeSignedPrimeProducerV1
import WeilRHImpliesFinalSignV13

/-!
# Optimized actual Weil–Schur global join

This module composes the EXISTING arbitrary-packet fine Gram constructor with
the EXISTING optimized weighted-Schur bound, using the genuine Weil pairing.
The optimized Q16.16 diagonal-minus-row margin is 34727/32768.

The universal mathematical input is the explicit producer `hselect`,
which selects a reconstruction with certified actual off-diagonal entries.
The premise is NOT constructed here. In particular, this module does not
assert unconditional RiemannHypothesis or provide an upstream formal_proof.
-/

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHOptimizedSchurGlobalJoinV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13

/-! ## Sharp scalar signed-defect route (no Schur or absolute-row assumption)

The actual mixed defect has an exact scalar criterion, irrespective of
the energies and relative locations of the atoms. This is strictly weaker
than the conservative 5671/3200 energy budget as a sufficient condition.
It is an identity, not a universal arithmetic estimate. The cluster
producer below supplies the exact budget on its proved domain.
-/

/-- Necessary and sufficient exact signed mixed budget for the genuine
finite Weil Gram, with no diagonal coercivity or matrix norm assumptions. -/
theorem actual_signed_defect_iff_packet_nonpositive
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      -(∑ i, (B (gs i) (gs i)).re) ↔
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
      (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  rw [hgram]
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect
  constructor <;> intro h <;> linarith

/-- Source-proved 9/64 cluster coercivity pays the exact signed budget.
No absolute values, weights or pairwise row bounds occur in the statement.
The common-center geometric hypothesis is preserved without weakening. -/
theorem actual_fine_cluster_sharp_signed_budget
    (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (centers : Fin (n + 1) → ℝ) (center : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hw : ∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
      (gs i) (centers i))
    (hnear : ∀ i, |centers i - center| ≤ (35 / 256 : ℝ)) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
      -(∑ i, (B (gs i) (gs i)).re) := by
  have h := AEGIS.RHActualMixedDefectV1.fine_cluster_nine_mixed_defect_opposite
    n gs centers center hm hw hnear
  have hE : 0 ≤ energy (packetSum (fun _ => (1 : ℂ)) gs).1 :=
    energy_nonnegative _
  linarith

/-- The existing optimized bound makes one actual reconstructed packet
nonpositive once the genuine mixed-entry and weighted-row estimates are
available. Unequal atom energies and arbitrary finite dimension are allowed. -/
theorem actual_packet_sum_nonpositive_of_optimized_rows
    {n : ℕ}
    (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (w : Fin (n + 1) → ℝ)
    (hc : ∀ i j, 0 ≤ c i j)
    (hzero : ∀ i, c i i = 0)
    (hsym : ∀ i j, c i j = c j i)
    (hw : ∀ i, 0 < w i)
    (hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤ c i j *
        (Real.sqrt (energy (gs i).1) *
          Real.sqrt (energy (gs j).1)))
    (hrow : ∀ i, ∑ j, c i j * (w j / w i) ≤
      (46688 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have hopt :=
    AEGIS.RHScaleRowCompositionV1.actual_optimized_weighted_schur_unequal_energy_from_fine_diagonals
      gs (fun _ => (1 : ℂ)) c w hc hzero hsym hw hd hcross hrow
  have henergy :
      0 ≤ ∑ i : Fin (n + 1), energy (gs i).1 * ‖(1 : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (energy_nonnegative (gs i).1) (sq_nonneg _))
  have hnonpos :
      -(34727 / 32768 : ℝ) *
        (∑ i : Fin (n + 1), energy (gs i).1 * ‖(1 : ℂ)‖ ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num) henergy
  exact hopt.trans hnonpos

/-- Universal sign consumer using a *selected* finite reconstruction, not
an arbitrary partition. The starting geometry and actual Weil Gram are
constructed by the existing source theorem. The explicit hselect obligation
may replace that partition with one certified weighted-Schur reconstruction.

This choice of quantifiers is essential: arbitrary fine decompositions may
contain repeated or nearly identical atoms and need not satisfy a strict
off-diagonal row budget. No universal analytic producer is assumed proved. -/
theorem riemannHypothesis_of_optimized_actual_row_producer
    (hselect :
      ∀ (g : WeilCompactSmoothGV1)
        (_hm : WeilMomentConditionsV1 g)
        (n : ℕ)
        (gs : Fin (n + 1) → WeilCompactSmoothGV1)
        (center : Fin (n + 1) → ℝ),
        (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
          (gs i) (center i)) →
        (∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
          -(B (gs i) (gs i)).re) →
        g = packetSum (fun _ => (1 : ℂ)) gs →
        ∃ (m : ℕ) (selected : Fin (m + 1) → WeilCompactSmoothGV1),
          g = packetSum (fun _ => (1 : ℂ)) selected ∧
          (∀ i, (5671 / 3200 : ℝ) * energy (selected i).1 ≤
            -(B (selected i) (selected i)).re) ∧
          ∃ (c : Fin (m + 1) → Fin (m + 1) → ℝ)
            (w : Fin (m + 1) → ℝ),
            (∀ i j, 0 ≤ c i j) ∧
            (∀ i, c i i = 0) ∧
            (∀ i j, c i j = c j i) ∧
            (∀ i, 0 < w i) ∧
            (∀ i j, i ≠ j →
              ‖B (selected i) (selected j)‖ ≤ c i j *
                (Real.sqrt (energy (selected i).1) *
                  Real.sqrt (energy (selected j).1))) ∧
            (∀ i, ∑ j, c i j * (w j / w i) ≤
              (46688 / 65536 : ℝ))) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro g hm
  obtain ⟨n, gs, center, _hmom, hd, hwidth, hpacket, _hgram⟩ :=
    AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram_with_support g hm
  obtain ⟨m, selected, hselected, hdiag, c, w, hc, hzero, hsym, hw,
    hcross, hrow⟩ :=
    hselect g hm n gs center hwidth hd hpacket
  have hsign :=
    actual_packet_sum_nonpositive_of_optimized_rows
      selected c w hc hzero hsym hw hdiag hcross hrow
  rw [hselected]
  change (B (packetSum (fun _ => (1 : ℂ)) selected)
    (packetSum (fun _ => (1 : ℂ)) selected)).re ≤ 0
  exact hsign


/-! ## Time slices: distinguish the exact shift ledger from its created Weil packet

The time coordinate is an integer spectral-translation label. The created
packet is the translated test function, with all genuine B-interactions
retained. The established common-window inequality immediately pays the
sharp signed defect. This does not assume or imply a global sign for
unrestricted time shifts.
-/

/-- Every finite family of exact femtosecond spectral translates of a
moment-zero narrow packet pays its entire REAL signed Weil mixed defect
whenever the established common-window span bound holds. Neither Schur
weights nor absolute off-diagonal bounds are used. -/
theorem actual_time_slice_sharp_signed_budget
    {n : ℕ} (g : WeilCompactSmoothGV1) (p origin center : ℝ)
    (ticks : Fin (n + 1) → ℤ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (1 / 256) origin)
    (hspan : ∀ i,
      |origin + AEGIS.RHTimeSliceWeilV1.fsLogSlice p (ticks i) - center| ≤
        (507 / 1280 : ℝ)) :
    AEGIS.RHActualMixedDefectV1.actualMixedDefect n
      (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks) ≤
      -(∑ i, (B
        (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks i)
        (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks i)).re) := by
  have hmargin :=
    AEGIS.RHTimeSliceWeilV1.timeSliceFamily_full_weighted_margin
      g p origin center ticks (fun _ => (1 : ℂ)) hm hw hspan
  have hfull :=
    AEGIS.RHTimeSliceWeilV1.timeSliceFamily_full_gram
      g p ticks (fun _ => (1 : ℂ))
  rw [← hfull] at hmargin
  have hE : 0 ≤ (1 / 16 : ℝ) *
      energy (packetSum (fun _ => (1 : ℂ))
        (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks)).1 :=
    mul_nonneg (by norm_num) (energy_nonnegative _)
  apply (actual_signed_defect_iff_packet_nonpositive
    (AEGIS.RHTimeSliceWeilV1.timeSliceFamily g p ticks)).mpr
  linarith

/-! ## Canonical RH equivalence using ONE sharp signed actual reconstruction

Unlike optimized Schur, this formulation has no hselect, no pointwise
absolute-value estimates and no diagonal-energy requirements.
The existential sign estimate is *precisely* the universal RH-equivalent
mathematical obligation, not an unconditionally proved producer.
-/

/-- The exact Mathlib RH target is equivalent to one signed actual Weil
finite reconstruction for each moment-zero source packet. No invented
matrix estimate, equal-energy reduction, or selected partition is assumed.
-/
theorem rh_iff_one_actual_sharp_signed_budget :
    RiemannHypothesis ↔
      ∀ (g : WeilCompactSmoothGV1), WeilMomentConditionsV1 g →
        ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
          g = packetSum (fun _ => (1 : ℂ)) gs ∧
          AEGIS.RHActualMixedDefectV1.actualMixedDefect n gs ≤
            -(∑ i, (B (gs i) (gs i)).re) := by
  constructor
  · intro hRH g hm
    obtain ⟨n, gs, _hmom, _hd, hpacket, hgram⟩ :=
      AEGIS.RHActualUniversalFineGramV1.every_moment_zero_packet_actual_fine_gram
        g hm
    refine ⟨n, gs, hpacket, ?_⟩
    have hfinal :
        (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 :=
      (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
        g hm).mpr
          ((AEGIS.WeilRHImpliesFinalSignV13.rh_implies_universal_v13 hRH) g hm)
    have hsum : (∑ i, ∑ j, B (gs i) (gs j)).re ≤ 0 := by
      rw [← hgram]
      exact hfinal
    apply (actual_signed_defect_iff_packet_nonpositive gs).mpr
    rw [B_packetSum]
    simpa using hsum
  · intro hcert
    apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
    intro g hm
    obtain ⟨n, gs, hpacket, hsigned⟩ := hcert g hm
    have hsign := (actual_signed_defect_iff_packet_nonpositive gs).mp hsigned
    rw [hpacket]
    change (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0
    exact hsign


/-! ## Exact nonlocal log-three creation of a time slice

The newly created packet at two integer seconds in the declared p=3
spectral clock is EXACTLY the arithmetic translate by 2*log 3.
The signed von Mangoldt/Arch theorem therefore applies with its
original source hypotheses, without any shared 9/64 window and without
a floating-point approximation of the temporal shift.
-/

theorem fsLogSlice_three_two_seconds_exact :
    AEGIS.RHTimeSliceWeilV1.fsLogSlice 3 2000000000000000 =
      2 * Real.log 3 := by
  norm_num [AEGIS.RHTimeSliceWeilV1.fsLogSlice]

/-- A genuine nonlocal two-time-slice Weil coercivity with no extra
prime-row or Schur premise. This is the source-proved two-log-three
von Mangoldt estimate transported to exact integer time slices. -/
theorem actual_two_log_three_time_slice_coercive
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (1 / 256 : ℝ) a) :
    (B
      (addPacket (AEGIS.RHTimeSliceWeilV1.timeSlicePacket g 3 0)
        (AEGIS.RHTimeSliceWeilV1.timeSlicePacket
          g 3 2000000000000000))
      (addPacket (AEGIS.RHTimeSliceWeilV1.timeSlicePacket g 3 0)
        (AEGIS.RHTimeSliceWeilV1.timeSlicePacket
          g 3 2000000000000000))).re ≤
      -(10517 / 4800 : ℝ) * energy g.1 := by
  simpa only [AEGIS.RHTimeSliceWeilV1.timeSlicePacket,
    AEGIS.RHTimeSliceWeilV1.fsLogSlice_zero,
    fsLogSlice_three_two_seconds_exact] using
      AEGIS.RHLogThreeSignedPrimeProducerV1.actual_two_log_three_gram_coercive
        g a hm hw

/-- The two created, far-separated actual Weil slices have a
nonpositive complete signed quadratic, including their mixed entry. -/
theorem actual_two_log_three_time_slice_nonpositive
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      g (1 / 256 : ℝ) a) :
    (B
      (addPacket (AEGIS.RHTimeSliceWeilV1.timeSlicePacket g 3 0)
        (AEGIS.RHTimeSliceWeilV1.timeSlicePacket
          g 3 2000000000000000))
      (addPacket (AEGIS.RHTimeSliceWeilV1.timeSlicePacket g 3 0)
        (AEGIS.RHTimeSliceWeilV1.timeSlicePacket
          g 3 2000000000000000))).re ≤ 0 := by
  have h := actual_two_log_three_time_slice_coercive g a hm hw
  exact h.trans (mul_nonpos_of_nonpos_of_nonneg
    (by norm_num) (energy_nonnegative g.1))

end AEGIS.RHOptimizedSchurGlobalJoinV1

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_signed_defect_iff_packet_nonpositive
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_fine_cluster_sharp_signed_budget
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_packet_sum_nonpositive_of_optimized_rows
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.riemannHypothesis_of_optimized_actual_row_producer

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_time_slice_sharp_signed_budget
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.rh_iff_one_actual_sharp_signed_budget

#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.fsLogSlice_three_two_seconds_exact
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_two_log_three_time_slice_coercive
#print axioms AEGIS.RHOptimizedSchurGlobalJoinV1.actual_two_log_three_time_slice_nonpositive
