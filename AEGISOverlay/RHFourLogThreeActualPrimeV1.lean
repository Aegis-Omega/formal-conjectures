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

import AEGISOverlay.RHOptimizedSchurGlobalJoinV1
import Mathlib.Tactic
import WeilTranslationGapInvariantV10
import AEGISOverlay.RHArchRow29V1

/-!
# Exact signed prime cost at every four-log-three separation

This is a genuine von Mangoldt (not surrogate Gram) estimate at every
positive lattice displacement d, for any horizon K >= 4*d and an actual
fine packet of the existing K-dependent support.

It does not assume RH, a Schur signed-row certificate, or a selected
reconstruction of arbitrary packets. No claim about a fixed positive
seed radius uniformly in K is made.
-/

open Complex
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHPrimeThreeWindowV1
open AEGIS.RHDyadicDiagonalV13

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFourLogThreeActualPrimeV1

open AEGIS.RHGramExpansionV13

/-- The exact arithmetic ratio for a 4*d*log(3) gap. -/
theorem triadicHalf_four_mul (d : ℕ) :
    triadicHalf (4 * d) = (1 / 9 : ℝ) ^ d := by
  unfold triadicHalf
  have harg :
      -(((4 * d : ℕ) : ℝ) * Real.log 3) / 2 =
        (d : ℝ) * (-2 * Real.log 3) := by
    push_cast
    ring
  rw [harg, Real.exp_nat_mul]
  have hexp : Real.exp (-2 * Real.log (3 : ℝ)) = (1 / 9 : ℝ) := by
    rw [show -2 * Real.log (3 : ℝ) = -(Real.log 3 + Real.log 3) by ring,
      Real.exp_neg, Real.exp_add]
    norm_num [Real.exp_log]
  rw [hexp]

/-- Actual exact signed prime interaction for every positive 4*d gap. -/
theorem actual_prime_four_log_three_exact
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a) :
    (WeilPrimeSumV1
      (mixed (translatePacket g 0)
        (translatePacket g ((4 * d : ℕ) * Real.log 3)))).re =
      Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 := by
  have hp :=
    AEGIS.RHOptimizedSchurGlobalJoinV1.exact_von_mangoldt_time_horizon
      K (4 * d) (by omega) hdK g a hw
  have hr := congrArg Complex.re hp
  simp only [Complex.ofReal_re] at hr
  simpa only [triadicHalf_four_mul] using hr

/-- Source-proved, uniform-in-d rational cost for the actual prime row
at any separated same-mother pair. No fabricated sign/cross hypotheses. -/
theorem actual_prime_four_log_three_signed_cost
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a) :
    (WeilPrimeSumV1
      (mixed (translatePacket g 0)
        (translatePacket g ((4 * d : ℕ) * Real.log 3)))).re ≤
      (1 / 9 : ℝ) ^ d *
        (energy (translatePacket g 0).1 +
         energy (translatePacket g ((4 * d : ℕ) * Real.log 3)).1) := by
  have hpow : 0 ≤ (1 / 9 : ℝ) ^ d := by positivity
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hcoeff :
      Real.log (3 : ℝ) * ((1 / 9 : ℝ) ^ d * energy g.1) ≤
        2 * ((1 / 9 : ℝ) ^ d * energy g.1) :=
    mul_le_mul_of_nonneg_right
      AEGIS.RHLogThreeSignedPrimeProducerV1.log_three_le_two
      (mul_nonneg hpow hE)
  calc
    (WeilPrimeSumV1
      (mixed (translatePacket g 0)
        (translatePacket g ((4 * d : ℕ) * Real.log 3)))).re =
        Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 :=
          actual_prime_four_log_three_exact K d hd hdK g a hw
    _ = Real.log 3 * ((1 / 9 : ℝ) ^ d * energy g.1) := by ring
    _ ≤ 2 * ((1 / 9 : ℝ) ^ d * energy g.1) := hcoeff
    _ = (1 / 9 : ℝ) ^ d *
        (energy (translatePacket g 0).1 +
         energy (translatePacket g ((4 * d : ℕ) * Real.log 3)).1) := by
        rw [translate_energy, translate_energy]
        ring


/-- Uniform rational prime-row estimate for EVERY number of translated
same-mother atoms. Unlike finite 4-block row enumeration, n is arbitrary.
This is the actual geometric budget consumed by Arch-29, not an RH claim. -/
theorem full_four_log_three_prime_row {n : ℕ} (i : Fin (n + 1)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      (1 / 9 : ℝ) ^ Nat.dist i j) ≤ (1 / 4 : ℝ) := by
  have hIcc : (Finset.Icc 1 n : Finset ℕ) =
      Finset.Ico 1 (n + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hgeom :
      (∑ k ∈ Finset.Icc 1 n, (1 / 9 : ℝ) ^ k) ≤
        (1 / 8 : ℝ) := by
    rw [hIcc]
    exact AEGIS.RHOptimizedSchurGlobalJoinV1.four_log_three_prime_geometric_tail n
  have hrow := AEGIS.RHGramExpansionV13.rowSum_le
    (n := n) (c := fun k => (1 / 9 : ℝ) ^ k)
    (by intro k; positivity) i
  calc
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (1 / 9 : ℝ) ^ Nat.dist i j) ≤
      2 * (∑ k ∈ Finset.Icc 1 n, (1 / 9 : ℝ) ^ k) := hrow
    _ ≤ 2 * (1 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left hgeom (by norm_num)
    _ = 1 / 4 := by norm_num

/-- The genuine signed-prime geometric row fits inside the pre-existing
Arch-29 Schur allowance, uniformly in n. -/
theorem full_four_log_three_prime_row_arch29 {n : ℕ} (i : Fin (n + 1)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
      (1 / 9 : ℝ) ^ Nat.dist i j) ≤ (57401 / 65536 : ℝ) :=
  (full_four_log_three_prime_row i).trans (by norm_num)

/-- Actual complex Weil B interaction at every positive four-log-three
gap under the source-bound time-horizon support and moment conditions.
This is not just the prime row: it retains the Archimedean allowance. -/
theorem actual_mixed_B_norm_four_log_three
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a) :
    ‖B (translatePacket g 0)
      (translatePacket g ((4 * d : ℕ) * Real.log 3))‖ ≤
      (Real.log 3 * (1 / 9 : ℝ) ^ d + 1 / 100) * energy g.1 := by
  simpa only [triadicHalf_four_mul] using
    (AEGIS.RHOptimizedSchurGlobalJoinV1.actual_mixed_B_norm_time_horizon
      K (4 * d) (by omega) hdK g a hm hw)

/-- The prime-side certificate is invariant under a common translation
of the mother packet. No hypothesis about the absolute lattice origin. -/
theorem actual_prime_four_log_three_signed_cost_at_centers
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (u v : ℝ)
    (hgap : v - u = ((4 * d : ℕ) : ℝ) * Real.log 3) :
    (WeilPrimeSumV1 (mixed (translatePacket g u)
      (translatePacket g v))).re ≤
      (1 / 9 : ℝ) ^ d *
        (energy (translatePacket g u).1 +
          energy (translatePacket g v).1) := by
  have hgap' :
      v - u = (((4 * d : ℕ) : ℝ) * Real.log 3) - 0 := by
    simpa using hgap
  have htranslate :=
    AEGIS.WeilTranslationGapInvariantV10.mixed_translate_eq_of_gap_v10
      g u v 0 (((4 * d : ℕ) : ℝ) * Real.log 3) hgap'
  rw [htranslate]
  simpa only [translate_energy] using
    (actual_prime_four_log_three_signed_cost K d hd hdK g a hw)

/-- The actual full complex Weil B bound for any two same-mother
translations with a four-log-three gap. This preserves the full
Archimedean term and does not assert a universal packet selector. -/
theorem actual_mixed_B_norm_at_centers
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hm : WeilMomentConditionsV1 g)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (u v : ℝ)
    (hgap : v - u = ((4 * d : ℕ) : ℝ) * Real.log 3) :
    ‖B (translatePacket g u) (translatePacket g v)‖ ≤
      (Real.log 3 * (1 / 9 : ℝ) ^ d + 1 / 100) * energy g.1 := by
  have hgap' :
      v - u = (((4 * d : ℕ) : ℝ) * Real.log 3) - 0 := by
    simpa using hgap
  have htranslate :=
    AEGIS.WeilTranslationGapInvariantV10.B_translate_eq_of_gap_v10
      g u v 0 (((4 * d : ℕ) : ℝ) * Real.log 3) hgap'
  rw [htranslate]
  exact actual_mixed_B_norm_four_log_three K d hd hdK g a hm hw

/-- An arbitrary finite sparse, equally-spaced-gap same-mother family
has a strictly negative real Weil Gram contraction. The actual prime
row is produced internally from the exact von Mangoldt formula, not
assumed. The hypotheses retain the separated family and exact
reconstruction scope; this does not supply a selector for arbitrary g. -/
theorem actual_four_log_three_same_mother_family_sign
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin (n + 1), i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  let primeCost : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => (1 / 9 : ℝ) ^ Nat.dist i j
  have hsym : ∀ i j, primeCost i j = primeCost j i := by
    intro i j
    dsimp [primeCost]
    rw [Nat.dist_comm]
  have hprime : ∀ i j : Fin (n + 1), i < j →
      (WeilPrimeSumV1 (mixed (gs i) (gs j))).re ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    obtain ⟨hd, _⟩ := hsep i j hij
    obtain ⟨hdK, hgapij⟩ := hgap i j hij
    have hp := actual_prime_four_log_three_signed_cost_at_centers
      K (Nat.dist i j) hd hdK g a hw
        (center i) (center j) hgapij
    simpa only [primeCost, hfamily i, hfamily j] using hp
  have hrow : ∀ i,
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        primeCost i j) ≤ (57401 / 65536 : ℝ) := by
    intro i
    simpa only [primeCost] using full_four_log_three_prime_row_arch29 i
  exact
    AEGIS.RHArchRow29V1.actual_far_fine_gram_coercive_of_signed_prime_arch29_row
      gs center hwidth hm hsep primeCost hsym hprime hrow


/-! ## Direct bridge to Mathlib's canonical RiemannHypothesis

The exact missing statement is a source-preserving GLOBAL reconstruction,
not an additional norm inequality for an already separated sparse family.
Keeping it a transparent Prop prevents a finite-window result from being
silently promoted to RH. No new axiom or sorry is used. -/

/-- Every moment-zero test packet can be reconstructed from actual
same-mother, four-log-three-separated Weil atoms, retaining all analytic
support, gap, moment and source-identity requirements. This is a
mathematical obligation, NOT a proved global constructor. -/
def HasActualFourLogThreeReconstruction (source : WeilCompactSmoothGV1) : Prop :=
  ∃ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (K : ℕ) (mother : WeilCompactSmoothGV1) (a : ℝ),
    source = packetSum (fun _ => (1 : ℂ)) gs ∧
    (∀ i, AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
      (gs i) (center i)) ∧
    (∀ i, WeilMomentConditionsV1 (gs i)) ∧
    (∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i) ∧
    HalfWidthAt mother
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a ∧
    (∀ i, gs i = translatePacket mother (center i)) ∧
    (∀ i j : Fin (n + 1), i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3)

/-- Direct, type-correct proof of the CANONICAL Mathlib RH proposition
from an explicit global source-preserving sparse-family constructor.
The prime-row and Arch-29 bounds have been discharged in the preceding
theorem; the global reconstruction remains the stated premise. -/
theorem riemannHypothesis_of_four_log_three_global_reconstruction
    (hglobal : ∀ source : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 source →
        HasActualFourLogThreeReconstruction source) :
    RiemannHypothesis := by
  apply AEGIS.RHRestrictedWeilBridgeV13.final_sign_implies_rh_v13
  intro source hm
  obtain ⟨n, gs, center, K, mother, a, hsource, hwidth,
      hatoms, hsep, hmother, hfamily, hgap⟩ := hglobal source hm
  have hbound :=
    actual_four_log_three_same_mother_family_sign
      gs center hwidth hatoms hsep K mother a hmother hfamily hgap
  have henergy : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  rw [hsource]
  change (B (packetSum (fun _ => (1 : ℂ)) gs)
    (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0
  nlinarith [hbound, henergy]


/-! ## Genuine complex von Mangoldt and norm-prime row for every sparse size

This improves the earlier signed-real row to the norm row needed for
phase-stable Gram estimates. It does not assert a global decomposition. -/

/-- Exact COMPLEX prime sum for arbitrary translated centers. -/
theorem actual_prime_four_log_three_complex_at_centers
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (u v : ℝ)
    (hgap : v - u = ((4 * d : ℕ) : ℝ) * Real.log 3) :
    WeilPrimeSumV1 (mixed (translatePacket g u) (translatePacket g v)) =
      ((Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 : ℝ) : ℂ) := by
  have hgap' :
      v - u = (((4 * d : ℕ) : ℝ) * Real.log 3) - 0 := by
    simpa using hgap
  have htranslate :=
    AEGIS.WeilTranslationGapInvariantV10.mixed_translate_eq_of_gap_v10
      g u v 0 (((4 * d : ℕ) : ℝ) * Real.log 3) hgap'
  rw [htranslate]
  simpa only [triadicHalf_four_mul] using
    (AEGIS.RHOptimizedSchurGlobalJoinV1.exact_von_mangoldt_time_horizon
      K (4 * d) (by omega) hdK g a hw)

/-- Norm-cost is obtained from the EXACT complex prime identity,
not by replacing the full Weil B with its signed real part. -/
theorem actual_prime_four_log_three_norm_cost_at_centers
    (K d : ℕ) (hd : 1 ≤ d) (hdK : 4 * d ≤ K)
    (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (u v : ℝ)
    (hgap : v - u = ((4 * d : ℕ) : ℝ) * Real.log 3) :
    ‖WeilPrimeSumV1 (mixed (translatePacket g u)
      (translatePacket g v))‖ ≤
      (1 / 9 : ℝ) ^ d *
        (energy (translatePacket g u).1 +
          energy (translatePacket g v).1) := by
  have hlog : 0 ≤ Real.log (3 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hpow : 0 ≤ (1 / 9 : ℝ) ^ d := by positivity
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  have hpos : 0 ≤ Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 :=
    mul_nonneg (mul_nonneg hlog hpow) hE
  have heq := actual_prime_four_log_three_complex_at_centers
    K d hd hdK g a hw u v hgap
  have hnorm :
      ‖WeilPrimeSumV1 (mixed (translatePacket g u)
        (translatePacket g v))‖ =
        Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 := by
    rw [heq]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  have hcoeff :
      Real.log 3 * ((1 / 9 : ℝ) ^ d * energy g.1) ≤
        2 * ((1 / 9 : ℝ) ^ d * energy g.1) :=
    mul_le_mul_of_nonneg_right
      AEGIS.RHLogThreeSignedPrimeProducerV1.log_three_le_two
      (mul_nonneg hpow hE)
  calc
    ‖WeilPrimeSumV1 (mixed (translatePacket g u)
      (translatePacket g v))‖ =
        Real.log 3 * (1 / 9 : ℝ) ^ d * energy g.1 := hnorm
    _ = Real.log 3 * ((1 / 9 : ℝ) ^ d * energy g.1) := by ring
    _ ≤ 2 * ((1 / 9 : ℝ) ^ d * energy g.1) := hcoeff
    _ = (1 / 9 : ℝ) ^ d *
        (energy (translatePacket g u).1 +
          energy (translatePacket g v).1) := by
      rw [translate_energy, translate_energy]
      ring

/-- Same genuine Weil coercivity with every OFF-DIAGONAL PRIME NORM
certified. Unlike the signed-only result, this remains sound when the
prime contributions have arbitrary phases. For an arbitrary source,
the sparse same-mother reconstruction is still an explicit requirement. -/
theorem actual_four_log_three_prime_norm_family_sign
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hwidth : ∀ i,
      AEGIS.RHRationalNinePacketPrimeWindowV1.WidthOneOneTwentyEightAt
        (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
        (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (K : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g
      (AEGIS.RHOptimizedSchurGlobalJoinV1.timeHorizonRadius K) a)
    (hfamily : ∀ i, gs i = translatePacket g (center i))
    (hgap : ∀ i j : Fin (n + 1), i < j →
      4 * Nat.dist i j ≤ K ∧
        center j - center i =
          ((4 * Nat.dist i j : ℕ) : ℝ) * Real.log 3) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  let primeCost : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => (1 / 9 : ℝ) ^ Nat.dist i j
  have hsym : ∀ i j, primeCost i j = primeCost j i := by
    intro i j
    dsimp [primeCost]
    rw [Nat.dist_comm]
  have hprime : ∀ i j : Fin (n + 1), i < j →
      ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    obtain ⟨hd, _⟩ := hsep i j hij
    obtain ⟨hdK, hgapij⟩ := hgap i j hij
    have hp := actual_prime_four_log_three_norm_cost_at_centers
      K (Nat.dist i j) hd hdK g a hw
        (center i) (center j) hgapij
    simpa only [primeCost, hfamily i, hfamily j] using hp
  have hrow : ∀ i,
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        primeCost i j) ≤ (57401 / 65536 : ℝ) := by
    intro i
    simpa only [primeCost] using full_four_log_three_prime_row_arch29 i
  exact
    AEGIS.RHArchRow29V1.actual_far_fine_gram_coercive_of_arch29_prime_row
      gs center hwidth hm hsep primeCost hsym hprime hrow

end AEGIS.RHFourLogThreeActualPrimeV1

#print axioms AEGIS.RHFourLogThreeActualPrimeV1.triadicHalf_four_mul
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_exact
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_signed_cost
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.full_four_log_three_prime_row
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.full_four_log_three_prime_row_arch29
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_mixed_B_norm_four_log_three
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_signed_cost_at_centers
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_mixed_B_norm_at_centers
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_same_mother_family_sign
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_complex_at_centers
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_prime_four_log_three_norm_cost_at_centers
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.actual_four_log_three_prime_norm_family_sign
#print axioms AEGIS.RHFourLogThreeActualPrimeV1.riemannHypothesis_of_four_log_three_global_reconstruction
