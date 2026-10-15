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

import RHFiniteActualGramJoinV1
import RHWindow693Over2000V1
import RHKreinTrigramAdaptiveV1

/-!
# Actual (not surrogate) finite Weil Gram sign on the certified window

This combines two existing independent *unconditional* Lean results:
* every moment-zero Weil packet admits an exact genuine finite Gram
  decomposition for ANY smooth partition of unity, preserving every mixed term;
* the actual arithmetic Weil form is nonpositive for every admissible packet
  of logarithmic half-width 693/2000.

For every such packet, every smooth partition yields genuine moment-zero
packets whose FULL actual Weil Hermitian Gram contraction has the certified
sign, without assuming any off-diagonal estimate or dropping B(i,j).

It does NOT establish that a weighted span of these partition atoms stays
within the certified class, nor PSD of arbitrary large-support packets.
-/

open scoped ContDiff BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHActualNarrowGramSignV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilMixedClosureV2 AEGIS.RHKreinFactorV13
open Set

/-- Exact full-matrix sign with every mixed coefficient retained, for any
smooth finite partition of an admissible packet in the certified 693/2000
window. This is NOT a global all-support RH positivity theorem. -/
theorem every_narrow_packet_actual_full_gram_nonpositive
    (n : ℕ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g (693 / 2000))
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x : ℝ, ∑ i : Fin (n + 1), χ i x = 1) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∑ i, ∑ j, B (gs i) (gs j)).re ≤ 0 := by
  obtain ⟨gs, hgs, hfull⟩ :=
    AEGIS.RHFiniteActualGramJoinV1.every_packet_actual_finite_gram
      n g hm χ hχ hpart
  refine ⟨gs, hgs, ?_⟩
  calc
    (∑ i, ∑ j, B (gs i) (gs j)).re =
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := hfull.symm
    _ ≤ 0 :=
      AEGIS.RHWindow693Over2000V1.window_693_over_2000_arithmetic_nonpositive_v1
        g hm hw


/-- The exact genuine Weil Gram contraction of ANY finite smooth partition
of a two-moment packet on the larger Trigram 2/5 logarithmic window is
nonpositive.  All cross terms B(gs i, gs j) remain in the conclusion:
nothing is dropped, averaged, or bounded by a surrogate coefficient.

This reuses the fully constructive moment-zero Krein partition and the
original actual arithmetic Trigram sign, with no added analytic premise.
It does NOT claim the same sign for packets of arbitrary support. -/
theorem every_two_fifths_packet_actual_full_gram_nonpositive
    (n : ℕ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.WeilWindowExhaustionV1.LogWindowContainsV1 g (2 / 5))
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x : ℝ, ∑ i : Fin (n + 1), χ i x = 1) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (∑ i, ∑ j, B (gs i) (gs j)).re ≤ 0 := by
  obtain ⟨gs, hgs, hfull⟩ :=
    AEGIS.RHFiniteActualGramJoinV1.every_packet_actual_finite_gram
      n g hm χ hχ hpart
  refine ⟨gs, hgs, ?_⟩
  calc
    (∑ i, ∑ j, B (gs i) (gs j)).re =
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re := hfull.symm
    _ ≤ 0 :=
      AEGIS.RHKreinTrigramAdaptiveV1.window_two_fifths_trigram_v1 g hm hw


/-- The Trigram zero-series margin holds with arbitrary logarithmic center,
so the original actual arithmetic Weil sign does not require recentering
the test packet to the origin. -/
theorem trigram_actual_arithmetic_nonpositive_at
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g (2 / 5) a) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ 0 := by
  have hmargin :=
    AEGIS.RHKreinTrigramAdaptiveV1.zero_quadratic_margin_trigram_v1
      g (2 / 5 : ℝ) a (by norm_num) (by norm_num) hw hm
  have henergy :
      0 ≤ (1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 :=
    mul_nonneg (by norm_num)
      (AEGIS.WeilDisjointEnergyV2.energy_nonnegative g.1)
  exact
    (AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      g hm).mpr (henergy.trans hmargin)

/-- The exact two-block identity converts Trigram's actual arithmetic
sign to a signed bound on the GENUINE Weil mixed entry, not a surrogate. -/
theorem trigram_actual_mixed_signed_from_sum
    (u v : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 (addPacket u v))
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u v) (2 / 5) a) :
    2 * (B u v).re ≤ -(B u u).re - (B v v).re := by
  have hsign :=
    trigram_actual_arithmetic_nonpositive_at (addPacket u v) a hm hw
  change (B (addPacket u v) (addPacket u v)).re ≤ 0 at hsign
  have hgram :=
    AEGIS.RHCofinalSchurAdapterV1.actual_two_block_gram_coefficients u v
  linarith

/-- The exact support geometry: 1/256 + (507/640)/2 = 2/5.
This increases the previously used 35/128 near-pair separation without
changing the supplied Weil packet or its moments. -/
theorem fine_width_into_trigram_midpoint
    (u : WeilCompactSmoothGV1) (a b : ℝ)
    (hu : AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (1 / 256) a)
    (hab : |a - b| ≤ (507 / 640 : ℝ)) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      u (2 / 5) ((a + b) / 2) := by
  change tsupport (lift u.1) ⊆
    Icc ((a + b) / 2 - 2 / 5) ((a + b) / 2 + 2 / 5)
  change tsupport (lift u.1) ⊆
    Icc (a - 1 / 256) (a + 1 / 256) at hu
  intro t ht
  obtain ⟨hlo, hhi⟩ := hu ht
  obtain ⟨hablo, habhi⟩ := abs_le.mp hab
  constructor <;> linarith

/-- Exact preservation of the Trigram logarithmic support under
arbitrary complex multiplication. -/
theorem trigram_width_scale
    (u : WeilCompactSmoothGV1) (z : ℂ) (a : ℝ)
    (hu : AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (2 / 5) a) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (scalePacket z u) (2 / 5) a := by
  change tsupport (lift (scalePacket z u).1) ⊆ Icc (a - 2 / 5) (a + 2 / 5)
  change tsupport (lift u.1) ⊆ Icc (a - 2 / 5) (a + 2 / 5) at hu
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

/-- Exact preservation of the Trigram window under packet addition. -/
theorem trigram_width_add
    (u v : WeilCompactSmoothGV1) (a : ℝ)
    (hu : AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (2 / 5) a)
    (hv : AEGIS.RHDyadicDiagonalV13.HalfWidthAt v (2 / 5) a) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u v) (2 / 5) a := by
  change tsupport (lift (addPacket u v).1) ⊆ Icc (a - 2 / 5) (a + 2 / 5)
  change tsupport (lift u.1) ⊆ Icc (a - 2 / 5) (a + 2 / 5) at hu
  change tsupport (lift v.1) ⊆ Icc (a - 2 / 5) (a + 2 / 5) at hv
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
    have hu0 : lift u.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxU
        exact hn (Or.inl hxU))
    have hv0 : lift v.1 x = 0 :=
      image_eq_zero_of_notMem_tsupport (by
        intro hxV
        exact hn (Or.inr hxV))
    exact hx (by simp [hu0, hv0])
  intro x hx
  rcases hs hx with hxU | hxV
  · exact hu hxU
  · exact hv hxV

/-- Any two fine atoms separated by at most 507/640 share the actual
Trigram 2/5 log window, even when their shapes are unrelated. -/
theorem nearby_fine_pair_shared_trigram_window
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hu : AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (1 / 256) a)
    (hv : AEGIS.RHDyadicDiagonalV13.HalfWidthAt v (1 / 256) b)
    (hab : |a - b| ≤ (507 / 640 : ℝ)) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      u (2 / 5) ((a + b) / 2) ∧
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      v (2 / 5) ((a + b) / 2) := by
  constructor
  · exact fine_width_into_trigram_midpoint u a b hu hab
  · have hba : |b - a| ≤ (507 / 640 : ℝ) := by
      simpa only [abs_sub_comm] using hab
    simpa only [add_comm] using
      (fine_width_into_trigram_midpoint v b a hv hba)

/-- True signed Weil B interaction of two distinct moment-zero fine
atoms at center separation at most 507/640. No near-pair cost premise. -/
theorem nearby_fine_pair_actual_mixed_signed_trigram
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hmu : WeilMomentConditionsV1 u)
    (hmv : WeilMomentConditionsV1 v)
    (hu : AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (1 / 256) a)
    (hv : AEGIS.RHDyadicDiagonalV13.HalfWidthAt v (1 / 256) b)
    (hab : |a - b| ≤ (507 / 640 : ℝ)) :
    2 * (B u v).re ≤ -(B u u).re - (B v v).re := by
  obtain ⟨hwu, hwv⟩ :=
    nearby_fine_pair_shared_trigram_window u v a b hu hv hab
  exact trigram_actual_mixed_signed_from_sum u v ((a + b) / 2)
    (momentConditions_addPacket_v10 u v hmu hmv)
    (trigram_width_add u v ((a + b) / 2) hwu hwv)


/-- The positive Trigram zero-series margin transfers EXACTLY, with
its 1/16 rational factor, to the genuine arithmetic side by the
original Weil autocorrelation explicit-formula identity. No sign-only
weakening or new analytic hypothesis is needed. -/
theorem trigram_actual_arithmetic_margin_at
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g (2 / 5) a) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤
      -(1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 := by
  have hmargin :=
    AEGIS.RHKreinTrigramAdaptiveV1.zero_quadratic_margin_trigram_v1
      g (2 / 5 : ℝ) a (by norm_num) (by norm_num) hw hm
  have hEF :=
    AEGIS.WeilAutocorrelationExplicitFormulaV10.autocorrelation_explicit_formula_v10 g hm
  rw [hEF]
  simp only [Complex.neg_re]
  linarith

/-- The EXACT full contracted Hermitian Weil Gram of every smooth
finite moment-zero Krein partition retains the 1/16 Trigram margin.
The original packet may be partitioned into arbitrarily many distinct
atoms; all off-diagonal entries remain in the double sum. -/
theorem every_trigram_packet_actual_full_gram_margin_at
    (n : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt g (2 / 5) a)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x : ℝ, ∑ i : Fin (n + 1), χ i x = 1) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy g.1 ≤
        -(∑ i, ∑ j, B (gs i) (gs j)).re := by
  obtain ⟨gs, hgs, hfull⟩ :=
    AEGIS.RHFiniteActualGramJoinV1.every_packet_actual_finite_gram
      n g hm χ hχ hpart
  refine ⟨gs, hgs, ?_⟩
  have hmargin := trigram_actual_arithmetic_margin_at g a hm hw
  rw [hfull] at hmargin
  linarith

/-- A *quantitative signed* bound for the true Weil mixed entry on
one common Trigram window, retaining the spectral-energy margin of
the sum itself rather than discarding it after proving its sign. -/
theorem trigram_actual_mixed_margin_from_sum
    (u v : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 (addPacket u v))
    (hw : AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (addPacket u v) (2 / 5) a) :
    2 * (B u v).re +
      (1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy (addPacket u v).1 ≤
      -(B u u).re - (B v v).re := by
  have hmargin :=
    trigram_actual_arithmetic_margin_at (addPacket u v) a hm hw
  change (B (addPacket u v) (addPacket u v)).re ≤
    -(1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy (addPacket u v).1
      at hmargin
  have hgram :=
    AEGIS.RHCofinalSchurAdapterV1.actual_two_block_gram_coefficients u v
  linarith

/-- The 507/640 center-distance theorem now has the full exact-rational
1/16 energy budget for two DIFFERENT moment-zero fine packets. -/
theorem nearby_fine_pair_actual_mixed_margin_trigram
    (u v : WeilCompactSmoothGV1) (a b : ℝ)
    (hmu : WeilMomentConditionsV1 u)
    (hmv : WeilMomentConditionsV1 v)
    (hu : AEGIS.RHDyadicDiagonalV13.HalfWidthAt u (1 / 256) a)
    (hv : AEGIS.RHDyadicDiagonalV13.HalfWidthAt v (1 / 256) b)
    (hab : |a - b| ≤ (507 / 640 : ℝ)) :
    2 * (B u v).re +
      (1 / 16 : ℝ) * AEGIS.WeilDisjointEnergyV2.energy (addPacket u v).1 ≤
      -(B u u).re - (B v v).re := by
  obtain ⟨hwu, hwv⟩ :=
    nearby_fine_pair_shared_trigram_window u v a b hu hv hab
  exact trigram_actual_mixed_margin_from_sum u v ((a + b) / 2)
    (momentConditions_addPacket_v10 u v hmu hmv)
    (trigram_width_add u v ((a + b) / 2) hwu hwv)

end AEGIS.RHActualNarrowGramSignV1

#print axioms AEGIS.RHActualNarrowGramSignV1.every_narrow_packet_actual_full_gram_nonpositive
#print axioms AEGIS.RHActualNarrowGramSignV1.every_two_fifths_packet_actual_full_gram_nonpositive
#print axioms AEGIS.RHActualNarrowGramSignV1.trigram_actual_arithmetic_nonpositive_at
#print axioms AEGIS.RHActualNarrowGramSignV1.trigram_actual_mixed_signed_from_sum
#print axioms AEGIS.RHActualNarrowGramSignV1.nearby_fine_pair_actual_mixed_signed_trigram
#print axioms AEGIS.RHActualNarrowGramSignV1.trigram_actual_arithmetic_margin_at
#print axioms AEGIS.RHActualNarrowGramSignV1.every_trigram_packet_actual_full_gram_margin_at
#print axioms AEGIS.RHActualNarrowGramSignV1.trigram_actual_mixed_margin_from_sum
#print axioms AEGIS.RHActualNarrowGramSignV1.nearby_fine_pair_actual_mixed_margin_trigram
