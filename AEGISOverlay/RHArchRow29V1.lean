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


import AEGISOverlay.RHArchGeometric145V1
import AEGISOverlay.RHActualUniversalFineGramV1
import AEGISOverlay.RHPrimeRowFirstTwoV1
import Mathlib

/-!
AEGIS Ω — rational improvement of the separated moment-zero Arch tail.
This file adds mathematical source candidates, NOT an unconditional RH claim.
All genuine von Mangoldt terms remain outside the Arch bound.
-/

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHArchRow29V1

open AEGIS.RHGramExpansionV13
open AEGIS.RHActualMixedDefectV1
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHRationalNinePacketPrimeWindowV1

/-- Dimension-free real-Weil coercivity with the sharper Arch envelope.
At each row the genuine prime cost may consume 57401/65536, while
the complete Arch contribution consumes at most 29/65536. This result
requires both an ordered-separated fine family and an actual prime
row certificate; it does not construct either for arbitrary packets. -/
theorem actual_far_fine_gram_coercive_of_arch29_prime_row
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hw : ∀ i, WidthOneOneTwentyEightAt (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
      (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (primeCost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, primeCost i j = primeCost j i)
    (hprime : ∀ i j : Fin (n + 1), i < j →
      ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1))
    (hprimeRow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      primeCost i j) ≤ (57401 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  let c : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j =>
    primeCost i j +
      ((1 / 32 : ℝ) * (54 / 53)) * ((1 / 145 : ℝ) ^ Nat.dist i j)
  have hc : ∀ i j, c i j = c j i := by
    intro i j
    dsimp [c]
    rw [hsym i j, Nat.dist_comm i j]
  have hforward (i j : Fin (n + 1)) (hij : i < j) :
      ‖B (gs i) (gs j)‖ ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    obtain ⟨hk, hgap⟩ := hsep i j hij
    have ha := actual_B_norm_le_prime_plus_arch145
      (gs i) (gs j) (center i) (center j)
      (hw i) (hw j) (hm i) (Nat.dist i j) hk hgap
    dsimp [c]
    calc
      ‖B (gs i) (gs j)‖ ≤
          ‖WeilPrimeSumV1 (mixed (gs i) (gs j))‖ +
          (((1 / 32 : ℝ) * (54 / 53)) *
            ((1 / 145 : ℝ) ^ Nat.dist i j)) *
              (energy (gs i).1 + energy (gs j).1) := ha
      _ ≤ primeCost i j * (energy (gs i).1 + energy (gs j).1) +
          (((1 / 32 : ℝ) * (54 / 53)) *
            ((1 / 145 : ℝ) ^ Nat.dist i j)) *
              (energy (gs i).1 + energy (gs j).1) :=
        add_le_add (hprime i j hij) le_rfl
      _ = (primeCost i j +
            ((1 / 32 : ℝ) * (54 / 53)) *
              ((1 / 145 : ℝ) ^ Nat.dist i j)) *
            (energy (gs i).1 + energy (gs j).1) := by ring
  have hcross : ∀ i j, i ≠ j →
      ‖B (gs i) (gs j)‖ ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hforward i j hijlt
    · have hb := hforward j i hjilt
      rw [B_hermitian, Complex.norm_conj]
      simpa only [hc j i,
        add_comm (energy (gs j).1) (energy (gs i).1)] using hb
  have hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      c i j) ≤ (57430 / 65536 : ℝ) := by
    intro i
    calc
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) =
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          primeCost i j) +
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          ((1 / 32 : ℝ) * (54 / 53)) *
            ((1 / 145 : ℝ) ^ Nat.dist i j)) := by
          simp only [c, Finset.sum_add_distrib]
      _ ≤ (57401 / 65536 : ℝ) + (29 / 65536 : ℝ) :=
        add_le_add (hprimeRow i) (geometric_arch_row_29 i)
      _ = (57430 / 65536 : ℝ) := by norm_num
  have hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re := by
    intro i
    exact AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3
      (gs i) (center i) (hw i)
  apply AEGIS.RHActualUniversalFineGramV1.actual_fine_gram_coercive_of_signed_real_row_certificate
    gs c hc hd
  · intro i j hij
    exact ((le_abs_self (B (gs i) (gs j)).re).trans
      (Complex.abs_re_le_norm (B (gs i) (gs j)))).trans (hcross i j hij)
  · exact hrow


/-! ## Signed prime-side Arch-29 certificate

The signed real part, not the norm of the actual von Mangoldt sum,
is all that is needed for the full genuine Weil Gram. Negative prime
interactions are preserved. Analytic control of their row sum remains
an explicit hypothesis, so the statement does not assert RH. -/

/-- Direct signed real-part bound for a genuinely separated fine pair.
The only relaxation is on the Archimedean remainder. -/
theorem actual_B_re_le_signed_prime_plus_arch145
    (p q : WeilCompactSmoothGV1) (a b : ℝ)
    (hp : WidthOneOneTwentyEightAt p a)
    (hq : WidthOneOneTwentyEightAt q b)
    (hm : WeilMomentConditionsV1 p)
    (k : ℕ) (hk : 1 ≤ k)
    (hsep : (65 / 32 : ℝ) * (k : ℝ) ≤ b - a) :
    (B p q).re ≤ (WeilPrimeSumV1 (mixed p q)).re +
      (((1 / 32 : ℝ) * (54 / 53)) * ((1 / 145 : ℝ) ^ k)) *
        (energy p.1 + energy q.1) := by
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hgap : Real.log 2 ≤ b - a := by
    linarith [AEGIS.WeilThreeBlockAnalyticConstantsV21.log_two_upper]
  have hzero :=
    distinct_fine_far_mixed_one_zero p q a b hp hq hgap
  have harch :=
    actual_arch_le_geometric_145 p q a b hp hq hm k hk hsep
  have heq :
      B p q = WeilPrimeSumV1 (mixed p q) +
        WeilArchimedeanIntegralV1 (mixed p q) := by
    unfold B WeilExplicitRightSideV1
    rw [hzero]
    ring
  rw [heq, Complex.add_re]
  exact add_le_add le_rfl
    (((le_abs_self (WeilArchimedeanIntegralV1 (mixed p q)).re).trans
      (Complex.abs_re_le_norm (WeilArchimedeanIntegralV1 (mixed p q)))).trans harch)

/-- Full genuine Weil sign with the sharper Arch-29 estimate using a
SIGNED real von Mangoldt row certificate. Unlike a norm-prime bound,
this preserves favorable negative real interactions. No universal
prime-row certificate or decomposition is postulated as a theorem. -/
theorem actual_far_fine_gram_coercive_of_signed_prime_arch29_row
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (hw : ∀ i, WidthOneOneTwentyEightAt (gs i) (center i))
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hsep : ∀ i j : Fin (n + 1), i < j →
      1 ≤ Nat.dist i j ∧
      (65 / 32 : ℝ) * (Nat.dist i j : ℝ) ≤ center j - center i)
    (primeCost : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, primeCost i j = primeCost j i)
    (hprime : ∀ i j : Fin (n + 1), i < j →
      (WeilPrimeSumV1 (mixed (gs i) (gs j))).re ≤
        primeCost i j * (energy (gs i).1 + energy (gs j).1))
    (hprimeRow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      primeCost i j) ≤ (57401 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  let c : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j =>
    primeCost i j +
      ((1 / 32 : ℝ) * (54 / 53)) * ((1 / 145 : ℝ) ^ Nat.dist i j)
  have hc : ∀ i j, c i j = c j i := by
    intro i j
    dsimp [c]
    rw [hsym i j, Nat.dist_comm i j]
  have hforward (i j : Fin (n + 1)) (hij : i < j) :
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    obtain ⟨hk, hgap⟩ := hsep i j hij
    have ha := actual_B_re_le_signed_prime_plus_arch145
      (gs i) (gs j) (center i) (center j)
      (hw i) (hw j) (hm i) (Nat.dist i j) hk hgap
    dsimp [c]
    calc
      (B (gs i) (gs j)).re ≤
          (WeilPrimeSumV1 (mixed (gs i) (gs j))).re +
          (((1 / 32 : ℝ) * (54 / 53)) *
            ((1 / 145 : ℝ) ^ Nat.dist i j)) *
              (energy (gs i).1 + energy (gs j).1) := ha
      _ ≤ primeCost i j * (energy (gs i).1 + energy (gs j).1) +
          (((1 / 32 : ℝ) * (54 / 53)) *
            ((1 / 145 : ℝ) ^ Nat.dist i j)) *
              (energy (gs i).1 + energy (gs j).1) :=
        add_le_add (hprime i j hij) le_rfl
      _ = (primeCost i j +
            ((1 / 32 : ℝ) * (54 / 53)) *
              ((1 / 145 : ℝ) ^ Nat.dist i j)) *
            (energy (gs i).1 + energy (gs j).1) := by ring
  have hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hforward i j hijlt
    · have hb := hforward j i hjilt
      have hre : (B (gs i) (gs j)).re =
          (B (gs j) (gs i)).re := by
        rw [B_hermitian, Complex.conj_re]
      rw [hre]
      calc
        (B (gs j) (gs i)).re ≤
            c j i * (energy (gs j).1 + energy (gs i).1) := hb
        _ = c i j * (energy (gs i).1 + energy (gs j).1) := by
          rw [hc j i, add_comm]
  have hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      c i j) ≤ (57430 / 65536 : ℝ) := by
    intro i
    calc
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) =
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          primeCost i j) +
        (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
          ((1 / 32 : ℝ) * (54 / 53)) *
            ((1 / 145 : ℝ) ^ Nat.dist i j)) := by
          simp only [c, Finset.sum_add_distrib]
      _ ≤ (57401 / 65536 : ℝ) + (29 / 65536 : ℝ) :=
        add_le_add (hprimeRow i) (geometric_arch_row_29 i)
      _ = (57430 / 65536 : ℝ) := by norm_num
  have hd : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re := by
    intro i
    exact AEGIS.RHFineDiagonalUpgradeV3.fine_diagonal_5671_over_3200_v3
      (gs i) (center i) (hw i)
  exact AEGIS.RHActualUniversalFineGramV1.actual_fine_gram_coercive_of_signed_real_row_certificate
    gs c hc hd hcross hrow

end AEGIS.RHArchRow29V1

#print axioms AEGIS.RHArchRow29V1.arch_kernel_geometric_145
#print axioms AEGIS.RHArchRow29V1.geometric_arch_row_29
#print axioms AEGIS.RHArchRow29V1.actual_arch_le_geometric_145

#print axioms AEGIS.RHArchRow29V1.actual_B_norm_le_prime_plus_arch145
#print axioms AEGIS.RHArchRow29V1.actual_far_fine_gram_coercive_of_arch29_prime_row

#print axioms AEGIS.RHArchRow29V1.actual_B_re_le_signed_prime_plus_arch145
#print axioms AEGIS.RHArchRow29V1.actual_far_fine_gram_coercive_of_signed_prime_arch29_row
