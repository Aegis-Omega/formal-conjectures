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

import AEGISOverlay.RHBaguaWalshV1
import AEGISOverlay.RHActualNarrowGramSignV1

/-!
# AEGIS Ω — exact Bagua/Walsh change of coordinates on the genuine Weil Gram

Eight arbitrary actual Weil packets form eight Walsh modes with the exact
integer 8×8 coefficients from RHBaguaWalshV1. All 64 genuine mixed entries
of B are retained. This module assumes neither translation invariance
under xor nor diagonalization of the actual arithmetic Weil operator.

For moment-zero packets sharing a single radius-2/5 logarithmic window,
the existing full weighted Trigram certificate transfers its exact 1/16
spectral energy margin to every complex combination of the eight modes.
The restriction to a common certified window remains explicit.
-/

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHBaguaActualWeilV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.RHGramExpansionV13
open AEGIS.RHBaguaWalshV1
open AEGIS.RHActualNarrowGramSignV1

/-- Eight Walsh modes made from eight *actual* Weil packets. -/
def baguaMode (gs : Fin 8 → WeilCompactSmoothGV1)
    (a : Fin 8) : WeilCompactSmoothGV1 :=
  packetSum (fun i : Fin 8 => (walsh8 a i : ℂ)) gs

/-- The actual transformed 8×8 Hermitian Weil Gram matrix. -/
def baguaActualGram (gs : Fin 8 → WeilCompactSmoothGV1)
    (a b : Fin 8) : ℂ :=
  B (baguaMode gs a) (baguaMode gs b)

/-- Each entry retains all 64 ORIGINAL actual Weil mixed coefficients,
not a sign proxy and not an assumed diagonal Walsh spectrum. -/
theorem bagua_actual_gram_exact
    (gs : Fin 8 → WeilCompactSmoothGV1) (a b : Fin 8) :
    baguaActualGram gs a b =
      ∑ i : Fin 8, ∑ j : Fin 8,
        (walsh8 a i : ℂ) * star (walsh8 b j : ℂ) *
          B (gs i) (gs j) := by
  unfold baguaActualGram baguaMode
  rw [B_packetSum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [B_packetSum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Hermitian symmetry is inherited from the original Weil pairing. -/
theorem bagua_actual_gram_hermitian
    (gs : Fin 8 → WeilCompactSmoothGV1) (a b : Fin 8) :
    baguaActualGram gs b a = conj (baguaActualGram gs a b) := by
  unfold baguaActualGram
  exact B_hermitian (baguaMode gs a) (baguaMode gs b)

/-- The two moment annihilations survive every Walsh mode. -/
theorem bagua_mode_moments
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i)) (a : Fin 8) :
    WeilMomentConditionsV1 (baguaMode gs a) := by
  unfold baguaMode
  exact trigram_moment_packetSum 7
    (fun i : Fin 8 => (walsh8 a i : ℂ)) gs hm

/-- The certified common Trigram support survives every Walsh mode. -/
theorem bagua_mode_window
    (gs : Fin 8 → WeilCompactSmoothGV1) (center : ℝ)
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (2 / 5) center) (a : Fin 8) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (baguaMode gs a) (2 / 5) center := by
  unfold baguaMode
  exact trigram_window_packetSum 7
    (fun i : Fin 8 => (walsh8 a i : ℂ)) gs center hwin

/-- All 64 mode-mode entries are the true coefficients of the full
complex-weighted Hermitian quadratic B of the transformed packets. -/
theorem bagua_actual_weighted_gram_exact
    (gs : Fin 8 → WeilCompactSmoothGV1) (z : Fin 8 → ℂ) :
    B (packetSum z (baguaMode gs))
      (packetSum z (baguaMode gs)) =
    ∑ a : Fin 8, ∑ b : Fin 8,
      z a * star (z b) * baguaActualGram gs a b := by
  simpa only [baguaActualGram] using
    (B_packetSum z (baguaMode gs))

/-- The existing actual Trigram coercivity, with no additional
cross-term bound, transfers to the COMPLETE Walsh-transformed Weil
Gram and EVERY complex amplitude vector in the eight-dimensional mode
space. All 64 mode-mode terms are retained, with exact 1/16 margin. -/
theorem bagua_actual_full_weighted_margin
    (gs : Fin 8 → WeilCompactSmoothGV1) (center : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (2 / 5) center)
    (z : Fin 8 → ℂ) :
    (1 / 16 : ℝ) *
      AEGIS.WeilDisjointEnergyV2.energy
        (packetSum z (baguaMode gs)).1 ≤
    -(∑ a : Fin 8, ∑ b : Fin 8,
      z a * star (z b) * baguaActualGram gs a b).re := by
  have hmModes : ∀ a, WeilMomentConditionsV1 (baguaMode gs a) :=
    fun a => bagua_mode_moments gs hm a
  have hwModes : ∀ a, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (baguaMode gs a) (2 / 5) center :=
    fun a => bagua_mode_window gs center hwin a
  simpa only [baguaActualGram] using
    (trigram_full_weighted_gram_margin 7 z
      (baguaMode gs) center hmModes hwModes)


/-- The complete sesquilinear pairing in Bagua/Walsh coordinates.
No assumption that even-odd cross blocks vanish is made. -/
def baguaGramBilinear
    (gs : Fin 8 → WeilCompactSmoothGV1)
    (u v : Fin 8 → ℂ) : ℂ :=
  ∑ a : Fin 8, ∑ b : Fin 8,
    u a * star (v b) * baguaActualGram gs a b

/-- Exact Q=2, p=2 complementary-sector decomposition of ALL 64
true Weil Gram coefficients. Four contributions occur: plus/plus,
minus/minus, plus/minus, and minus/plus. In particular the latter
two actual mixed blocks are NOT silently assumed to be zero. -/
theorem bagua_sector_four_block_exact
    (gs : Fin 8 → WeilCompactSmoothGV1) (z : Fin 8 → ℂ) :
    baguaGramBilinear gs z z =
      baguaGramBilinear gs (baguaPlus z) (baguaPlus z) +
      baguaGramBilinear gs (baguaMinus z) (baguaMinus z) +
      baguaGramBilinear gs (baguaPlus z) (baguaMinus z) +
      baguaGramBilinear gs (baguaMinus z) (baguaPlus z) := by
  unfold baguaGramBilinear
  calc
    (∑ a : Fin 8, ∑ b : Fin 8,
      z a * star (z b) * baguaActualGram gs a b) =
      ∑ a : Fin 8, ∑ b : Fin 8,
        (baguaPlus z a + baguaMinus z a) *
          star (baguaPlus z b + baguaMinus z b) *
            baguaActualGram gs a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [bagua_reconstruct z a, bagua_reconstruct z b]
    _ = (∑ a : Fin 8, ∑ b : Fin 8,
          baguaPlus z a * star (baguaPlus z b) * baguaActualGram gs a b) +
        (∑ a : Fin 8, ∑ b : Fin 8,
          baguaMinus z a * star (baguaMinus z b) * baguaActualGram gs a b) +
        (∑ a : Fin 8, ∑ b : Fin 8,
          baguaPlus z a * star (baguaMinus z b) * baguaActualGram gs a b) +
        (∑ a : Fin 8, ∑ b : Fin 8,
          baguaMinus z a * star (baguaPlus z b) * baguaActualGram gs a b) := by
      simp only [star_add, add_mul, mul_add, Finset.sum_add_distrib]
      ring

/-- The four-sector identity is about the exact original B operator
applied to actual Walsh packets, not merely an abstract matrix proxy. -/
theorem bagua_actual_weil_four_sector_identity
    (gs : Fin 8 → WeilCompactSmoothGV1) (z : Fin 8 → ℂ) :
    B (packetSum z (baguaMode gs))
      (packetSum z (baguaMode gs)) =
      baguaGramBilinear gs (baguaPlus z) (baguaPlus z) +
      baguaGramBilinear gs (baguaMinus z) (baguaMinus z) +
      baguaGramBilinear gs (baguaPlus z) (baguaMinus z) +
      baguaGramBilinear gs (baguaMinus z) (baguaPlus z) := by
  calc
    B (packetSum z (baguaMode gs))
        (packetSum z (baguaMode gs)) =
      baguaGramBilinear gs z z := by
        simpa only [baguaGramBilinear] using
          bagua_actual_weighted_gram_exact gs z
    _ = _ := bagua_sector_four_block_exact gs z


/-! ## Genuine complementary coupling, not an assumed zero cross block

The Walsh/Bagua four-sector identity above keeps the +/− interactions.
Here the existing quantitative Trigram theorem controls their TRUE Weil
coefficient for arbitrary complex relative phase. This applies to the
entire eight-mode packet family, including every original mixed entry,
provided all source packets lie in the SAME certified 2/5 log window.
No commutation or block-diagonality of the arithmetic Weil B is assumed. -/

/-- Opposite-pair even packet in the existing genuine Walsh mode basis. -/
def baguaEvenPacket (gs : Fin 8 → WeilCompactSmoothGV1)
    (z : Fin 8 → ℂ) : WeilCompactSmoothGV1 :=
  packetSum (baguaPlus z) (baguaMode gs)

/-- Opposite-pair odd packet in the existing genuine Walsh mode basis. -/
def baguaOddPacket (gs : Fin 8 → WeilCompactSmoothGV1)
    (z : Fin 8 → ℂ) : WeilCompactSmoothGV1 :=
  packetSum (baguaMinus z) (baguaMode gs)

/-- The two exact complement modes inherit the TWO moment annihilations. -/
theorem bagua_both_complementary_moments
    (gs : Fin 8 → WeilCompactSmoothGV1) (z : Fin 8 → ℂ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i)) :
    WeilMomentConditionsV1 (baguaEvenPacket gs z) ∧
    WeilMomentConditionsV1 (baguaOddPacket gs z) := by
  constructor
  · unfold baguaEvenPacket
    exact trigram_moment_packetSum 7 (baguaPlus z) (baguaMode gs)
      (fun a => bagua_mode_moments gs hm a)
  · unfold baguaOddPacket
    exact trigram_moment_packetSum 7 (baguaMinus z) (baguaMode gs)
      (fun a => bagua_mode_moments gs hm a)

/-- The same 2/5 window survives both complementation projections. -/
theorem bagua_both_complementary_windows
    (gs : Fin 8 → WeilCompactSmoothGV1) (z : Fin 8 → ℂ)
    (center : ℝ)
    (hw : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (2 / 5) center) :
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (baguaEvenPacket gs z) (2 / 5) center ∧
    AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (baguaOddPacket gs z) (2 / 5) center := by
  constructor
  · unfold baguaEvenPacket
    exact trigram_window_packetSum 7 (baguaPlus z) (baguaMode gs)
      center (fun a => bagua_mode_window gs center hw a)
  · unfold baguaOddPacket
    exact trigram_window_packetSum 7 (baguaMinus z) (baguaMode gs)
      center (fun a => bagua_mode_window gs center hw a)

/-- Quantitative TRUE Weil +/− coupling. For every complex phase c,
the complete real mixed entry has an exact Trigram energy budget.
Thus the four Abjad phases 1, -1, I, -I are all covered without
silently discarding either cross block or introducing a new premise.
This is a signed margin, stronger than mere reconstruction. -/
theorem bagua_complementary_phase_coupling_margin
    (gs : Fin 8 → WeilCompactSmoothGV1) (center : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hw : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (2 / 5) center)
    (z : Fin 8 → ℂ) (phase : ℂ) :
    2 * (B (baguaEvenPacket gs z)
          (scalePacket phase (baguaOddPacket gs z))).re +
      (1 / 16 : ℝ) *
        AEGIS.WeilDisjointEnergyV2.energy
          (addPacket (baguaEvenPacket gs z)
            (scalePacket phase (baguaOddPacket gs z))).1 ≤
      -(B (baguaEvenPacket gs z) (baguaEvenPacket gs z)).re -
        (B (scalePacket phase (baguaOddPacket gs z))
          (scalePacket phase (baguaOddPacket gs z))).re := by
  obtain ⟨hmu, hmv⟩ := bagua_both_complementary_moments gs z hm
  obtain ⟨hwu, hwv⟩ := bagua_both_complementary_windows gs z center hw
  have hphaseMom :
      WeilMomentConditionsV1
        (scalePacket phase (baguaOddPacket gs z)) :=
    momentConditions_scalePacket_v10 phase (baguaOddPacket gs z) hmv
  have hphaseWin :
      AEGIS.RHDyadicDiagonalV13.HalfWidthAt
        (scalePacket phase (baguaOddPacket gs z)) (2 / 5) center :=
    trigram_width_scale (baguaOddPacket gs z) phase center hwv
  exact trigram_actual_mixed_margin_from_sum
    (baguaEvenPacket gs z)
    (scalePacket phase (baguaOddPacket gs z)) center
    (momentConditions_addPacket_v10 _ _ hmu hphaseMom)
    (trigram_width_add _ _ center hwu hphaseWin)


/-! ## Exact opposition in the Walsh character basis

Bagua opposite-index involution i ↦ 7-i acts on the ORIGINAL binary
packet labels. This is distinct from applying the same involution to
Walsh MODE labels. The Walsh matrix diagonalizes original-index
complementation, with precisely four positive and four negative
eigencharacters. No invariance of the ACTUAL Weil pairing under this
index permutation is postulated. -/

/-- Parity of the three binary line labels, as an exact ±1 integer. -/
def baguaCharacterParity (a : Fin 8) : ℤ :=
  if (a.val % 2 + (a.val / 2) % 2 +
      (a.val / 4) % 2) % 2 = 0 then 1 else -1

/-- Opposing all three bits multiplies a Walsh character by its
integer parity eigenvalue. This holds for ALL 64 character entries. -/
theorem bagua_walsh_opposite_character (a i : Fin 8) :
    walsh8 a (baguaOpp i) =
      baguaCharacterParity a * walsh8 a i := by
  fin_cases a <;> fin_cases i <;> decide

/-- EXACT Q=2, p=2 count: four complement-even and four
complement-odd Walsh characters, verified on the complete carrier. -/
theorem bagua_walsh_opposite_four_plus_four :
    (Finset.univ.filter
      (fun a : Fin 8 => baguaCharacterParity a = 1)).card = 4 ∧
    (Finset.univ.filter
      (fun a : Fin 8 => baguaCharacterParity a = -1)).card = 4 := by
  decide

/-- H C H = 8 diag(1,-1,-1,1,-1,1,1,-1), where C sends
i to 7-i. The entire original 8×8 complementary coupling
is preserved, rather than postulated to have vanishing cross terms. -/
theorem bagua_walsh_complement_cross (a b : Fin 8) :
    (∑ i : Fin 8, walsh8 a i * walsh8 (baguaOpp i) b) =
      if a = b then (8 : ℤ) * baguaCharacterParity b else 0 := by
  fin_cases a <;> fin_cases b <;> decide

end AEGIS.RHBaguaActualWeilV1

#print axioms AEGIS.RHBaguaActualWeilV1.bagua_actual_gram_exact
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_actual_gram_hermitian
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_mode_moments
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_mode_window
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_actual_weighted_gram_exact
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_actual_full_weighted_margin
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_sector_four_block_exact
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_actual_weil_four_sector_identity

#print axioms AEGIS.RHBaguaActualWeilV1.bagua_both_complementary_moments
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_both_complementary_windows
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_complementary_phase_coupling_margin
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_walsh_opposite_character
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_walsh_opposite_four_plus_four
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_walsh_complement_cross
