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
import RHRationalNinePacketPrimeWindowV1
import RHGramExpansionV13
import RHFineMomentPacketV3
import RestrictedWeilCriterionKernelBridgeV10

/-!
# Sparse width-1/128 reconstructions do not cover every moment-zero packet

`AEGISOverlay/RHFourLogThreeWeightedRHBridgeV1.riemannHypothesis_of_weighted_four_log_three_reconstruction`
assumes that every moment-zero packet is a sum `packetSum z gs` of atoms `gs i` of log width `1/128`
(`WidthOneOneTwentyEightAt (gs i) (center i)`), whose centers satisfy
`(65/32) · dist(i, j) ≤ center j − center i` for `i < j`. A sum of such atoms vanishes in log
coordinates outside the intervals `[center i − 1/256, center i + 1/256]`, which are more than `2`
apart, so it cannot be nonzero at two log points at distance `1`.

`twoFine = gFine + translatePacket gFine 1` is moment-zero and nonzero at `t₀` and `t₀ + 1`
(`twoFine_two_points`), so `not_all_sparse_reconstructions` refutes the part of that premise used
here: the source, the atoms and the spacing. The consumer theorem can therefore never be applied.
Nothing here concerns RH itself.
-/

open Set Complex

set_option autoImplicit false

noncomputable section

namespace AEGIS.RHSparseReconstructionObstructionV1

open AEGIS.WeilMixedAlgebraV2 AEGIS.RHGramExpansionV13 AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHRationalNinePacketPrimeWindowV1 AEGIS.RHFineMomentPacketV3
open AEGIS.WeilLogCoordinateIsometryV21 AEGIS.RestrictedWeilCriterionKernelBridgeV10

theorem logLift_addPacket (a b : WeilCompactSmoothGV1) (t : ℝ) :
    logLift (addPacket a b).1 t = logLift a.1 t + logLift b.1 t := by
  show (Real.exp (t / 2) : ℂ) * (a.1 (Real.exp t) + b.1 (Real.exp t)) =
    (Real.exp (t / 2) : ℂ) * a.1 (Real.exp t) + (Real.exp (t / 2) : ℂ) * b.1 (Real.exp t)
  ring

theorem logLift_scalePacket (z : ℂ) (a : WeilCompactSmoothGV1) (t : ℝ) :
    logLift (scalePacket z a).1 t = z * logLift a.1 t := by
  show (Real.exp (t / 2) : ℂ) * (z * a.1 (Real.exp t)) = z * ((Real.exp (t / 2) : ℂ) * a.1 (Real.exp t))
  ring

/-- A point where a packet sum is nonzero lies in the support of one of its atoms. -/
theorem exists_ne_of_packetSum_ne :
    ∀ {n : ℕ} (z : Fin (n + 1) → ℂ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) (t : ℝ),
      logLift (packetSum z gs).1 t ≠ 0 → ∃ i, logLift (gs i).1 t ≠ 0
  | 0, z, gs, t, h => by
      refine ⟨0, fun h0 => h ?_⟩
      show logLift (scalePacket (z 0) (gs 0)).1 t = 0
      rw [logLift_scalePacket, h0, mul_zero]
  | n + 1, z, gs, t, h => by
      have hdef : packetSum z gs =
          addPacket (packetSum (fun i => z i.castSucc) (fun i => gs i.castSucc))
            (scalePacket (z (Fin.last (n + 1))) (gs (Fin.last (n + 1)))) := rfl
      rw [hdef, logLift_addPacket, logLift_scalePacket] at h
      by_cases h1 : logLift (packetSum (fun i => z i.castSucc) (fun i => gs i.castSucc)).1 t = 0
      · rw [h1, zero_add] at h
        exact ⟨Fin.last (n + 1), fun h2 => h (by rw [h2, mul_zero])⟩
      · obtain ⟨i, hi⟩ :=
          exists_ne_of_packetSum_ne (fun i => z i.castSucc) (fun i => gs i.castSucc) t h1
        exact ⟨i.castSucc, hi⟩

theorem mem_Icc_of_width {g : WeilCompactSmoothGV1} {c t : ℝ}
    (hw : WidthOneOneTwentyEightAt g c) (h : logLift g.1 t ≠ 0) :
    t ∈ Icc (c - 1 / 256) (c + 1 / 256) :=
  hw (subset_tsupport _ h)

/-- No sum of spaced width-`1/128` atoms is nonzero at two log points at distance `1`. -/
theorem no_reconstruction_of_two_points (source : WeilCompactSmoothGV1) (t₀ : ℝ)
    (h₀ : logLift source.1 t₀ ≠ 0) (h₁ : logLift source.1 (t₀ + 1) ≠ 0)
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1) (z : Fin (n + 1) → ℂ)
    (center : Fin (n + 1) → ℝ) (hsrc : source = packetSum z gs)
    (hw : ∀ i, WidthOneOneTwentyEightAt (gs i) (center i))
    (hsp : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧ (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i) :
    False := by
  subst hsrc
  obtain ⟨i, hi⟩ := exists_ne_of_packetSum_ne z gs t₀ h₀
  obtain ⟨j, hj⟩ := exists_ne_of_packetSum_ne z gs (t₀ + 1) h₁
  obtain ⟨hi1, hi2⟩ := mem_Icc_of_width (hw i) hi
  obtain ⟨hj1, hj2⟩ := mem_Icc_of_width (hw j) hj
  rcases lt_trichotomy i j with hij | hij | hij
  · obtain ⟨hd, hc⟩ := hsp i j hij
    have hd' : (1 : ℝ) ≤ (Nat.dist i j : ℝ) := by exact_mod_cast hd
    linarith
  · subst hij
    linarith
  · obtain ⟨hd, hc⟩ := hsp j i hij
    have hd' : (1 : ℝ) ≤ (Nat.dist j i : ℝ) := by exact_mod_cast hd
    linarith

/-- `gFine + T₁ gFine`. -/
def twoFine : WeilCompactSmoothGV1 :=
  addPacket gFine (scalePacket 1 (translatePacket gFine 1))

theorem twoFine_moments : WeilMomentConditionsV1 twoFine :=
  addPacket_preserves_moments_v10 _ _ gFine_moments_v3
    (scalePacket_preserves_moments_v10 1 _ (translate_preserves_moments gFine 1 gFine_moments_v3))

theorem twoFine_two_points :
    ∃ t₀ : ℝ, logLift twoFine.1 t₀ ≠ 0 ∧ logLift twoFine.1 (t₀ + 1) ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp gFine_ne_zero_v3
  have hxpos : 0 < x := gFine.2.2.2 (subset_tsupport _ hx)
  have hL : logLift gFine.1 (Real.log x) ≠ 0 := by
    show (Real.exp (Real.log x / 2) : ℂ) * gFine.1 (Real.exp (Real.log x)) ≠ 0
    rw [Real.exp_log hxpos]
    exact mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne') hx
  obtain ⟨h1, h2⟩ := mem_Icc_of_width gFine_width_one_one_twenty_eight_v1 hL
  have hzero : ∀ s : ℝ, (s < -(1 / 256) ∨ 1 / 256 < s) → logLift gFine.1 s = 0 := by
    intro s hs
    by_contra hne
    obtain ⟨k1, k2⟩ := mem_Icc_of_width gFine_width_one_one_twenty_eight_v1 hne
    rcases hs with hs | hs <;> linarith
  refine ⟨Real.log x, ?_, ?_⟩
  · rw [twoFine, logLift_addPacket, logLift_scalePacket, logLift_translate,
      hzero (Real.log x - 1) (Or.inl (by linarith)), mul_zero, add_zero]
    exact hL
  · rw [twoFine, logLift_addPacket, logLift_scalePacket, logLift_translate,
      hzero (Real.log x + 1) (Or.inr (by linarith)), zero_add, one_mul,
      show Real.log x + 1 - 1 = Real.log x by ring]
    exact hL

/-- The source, atom and spacing part of the premise of
`riemannHypothesis_of_weighted_four_log_three_reconstruction` is false. -/
theorem not_all_sparse_reconstructions :
    ¬ ∀ source : WeilCompactSmoothGV1, WeilMomentConditionsV1 source →
      ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) (z : Fin (n + 1) → ℂ)
        (center : Fin (n + 1) → ℝ),
        source = packetSum z gs ∧
        (∀ i, WidthOneOneTwentyEightAt (gs i) (center i)) ∧
        (∀ i j : Fin (n + 1), i < j →
          1 ≤ Nat.dist i j ∧ (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i) := by
  intro h
  obtain ⟨t₀, h₀, h₁⟩ := twoFine_two_points
  obtain ⟨n, gs, z, center, hs, hw, hsp⟩ := h twoFine twoFine_moments
  exact no_reconstruction_of_two_points twoFine t₀ h₀ h₁ gs z center hs hw hsp

end AEGIS.RHSparseReconstructionObstructionV1

#print axioms AEGIS.RHSparseReconstructionObstructionV1.no_reconstruction_of_two_points
#print axioms AEGIS.RHSparseReconstructionObstructionV1.twoFine_two_points
#print axioms AEGIS.RHSparseReconstructionObstructionV1.not_all_sparse_reconstructions
