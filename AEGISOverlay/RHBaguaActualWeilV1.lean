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

end AEGIS.RHBaguaActualWeilV1

#print axioms AEGIS.RHBaguaActualWeilV1.bagua_actual_gram_exact
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_actual_gram_hermitian
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_mode_moments
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_mode_window
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_actual_weighted_gram_exact
#print axioms AEGIS.RHBaguaActualWeilV1.bagua_actual_full_weighted_margin
