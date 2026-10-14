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

import RHKreinMultiplicativeTransportV1
import RHGramExpansionV13
import Mathlib

/-!
# AEGIS Ω: actual finite Krein atoms to actual Weil Gram matrix

This integrates two pre-existing, *unconditional* source theorems:
1. Every moment-zero packet has an exact finite decomposition into genuine
   moment-zero Weil packets for each smooth finite partition of unity.
2. The actual sesquilinear Weil form B of a packetSum is its exact finite
   Hermitian Gram matrix, including every off-diagonal/mixed term.

This closes the representation/identity interface only. It makes no claim
that the arbitrary finite Gram matrix has the requisite sign or that any
row-sum, Schur, or cofinal estimate is unconditionally certified.
AUTHORITY_EFFECT = NONE; RH_PROVEN = FALSE.
-/

open Set Finset Complex
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFiniteActualGramJoinV1

open AEGIS.RHLocalKreinPartitionV1
open AEGIS.RHKreinMultiplicativeTransportV1
open AEGIS.RHGramExpansionV13
open AEGIS.WeilMixedAlgebraV2

/-- The existing recursively-defined `packetSum` is exactly the pointwise
sum of its genuine packets when all coefficients are 1. -/
theorem packetSum_one_apply :
    ∀ (n : ℕ) (gs : Fin (n + 1) → WeilCompactSmoothGV1),
      (packetSum (fun _ => (1 : ℂ)) gs).1 =
        (fun x => ∑ i, (gs i).1 x) := by
  intro n
  induction n with
  | zero =>
      intro gs
      funext x
      simp [packetSum, scalePacket]
  | succ n ih =>
      intro gs
      funext x
      have hprev := congrFun (ih (fun i : Fin (n + 1) => gs i.castSucc)) x
      change
        (packetSum (fun _ => (1 : ℂ))
          (fun i : Fin (n + 1) => gs i.castSucc)).1 x +
          (1 : ℂ) * (gs (Fin.last (n + 1))).1 x =
        ∑ i : Fin (n + 2), (gs i).1 x
      rw [Fin.sum_univ_castSucc]
      simpa only [one_mul] using
        congrArg (fun t : ℂ => t + (gs (Fin.last (n + 1))).1 x) hprev

/-- Every moment-zero packet, for *any* smooth finite partition of unity,
is exactly a true Weil Gram quadratic of actual packets. This theorem does
not discard the mixed B terms or replace the actual Weil form by a surrogate. -/
theorem every_packet_actual_finite_gram
    (n : ℕ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (χ : Fin (n + 1) → ℝ → ℂ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hpart : ∀ x : ℝ, ∑ i : Fin (n + 1), χ i x = 1) :
    ∃ gs : Fin (n + 1) → WeilCompactSmoothGV1,
      (∀ i, WeilMomentConditionsV1 (gs i)) ∧
      (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
  classical
  obtain ⟨gs, hgs, hsum⟩ :=
    every_moment_zero_packet_finite_actual_weil_partition
      (Finset.univ : Finset (Fin (n + 1))) g hm χ hχ (by
        intro x
        simpa using hpart x)
  refine ⟨gs, ?_, ?_⟩
  · intro i
    exact hgs i (Finset.mem_univ i)
  · have hpacket : g = packetSum (fun _ => (1 : ℂ)) gs := by
      apply Subtype.ext
      calc
        g.1 = (fun x => ∑ i, (gs i).1 x) := by simpa using hsum
        _ = (packetSum (fun _ => (1 : ℂ)) gs).1 :=
          (packetSum_one_apply n gs).symm
    rw [hpacket]
    change
      (B (packetSum (fun _ => (1 : ℂ)) gs)
        (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re
    rw [B_packetSum]
    simp

end AEGIS.RHFiniteActualGramJoinV1

#print axioms AEGIS.RHFiniteActualGramJoinV1.packetSum_one_apply
#print axioms AEGIS.RHFiniteActualGramJoinV1.every_packet_actual_finite_gram
