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

import Mathlib

open Finset
open scoped BigOperators
set_option autoImplicit false

namespace AEGIS.RHResonanceRowWeightedSumV1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem offdiag_eq (f : ι → ι → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, f i j = (∑ i, ∑ j, f i j) - ∑ i, f i i := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_erase_eq_sub (Finset.mem_univ i))

theorem offdiag_swap (f : ι → ι → ℝ) :
    ∑ i, ∑ j ∈ univ.erase i, f i j = ∑ i, ∑ j ∈ univ.erase i, f j i := by
  simp only [offdiag_eq]
  rw [Finset.sum_comm]

/-- Weighted row sum for a resonance-row hypothesis of the shape of `hresidual`
    (`AEGISOverlay/RHPrimeFreeRecompositionJoinV1.lean`), with abstract data:
    `E` the energies, `Bre` the real parts of the mixed form, `LF` the
    log-free relation on pairs, `c` the fixed log-free cost, `β` the row
    budget and `κ` the diagonal constant.

    The conclusion keeps the log-free bracket `c * (E i + E j) - Bre i j`
    instead of discarding it. No bound on `Bre` for log-free pairs is used. -/
theorem weighted_row_sum
    (E : ι → ℝ) (Bre residual : ι → ι → ℝ) (LF : ι → ι → Prop) [DecidableRel LF]
    (c β κ : ℝ)
    (hE : ∀ i, 0 ≤ E i)
    (hLF : ∀ i j, LF i j ↔ LF j i)
    (hrsymm : ∀ i j, residual i j = residual j i)
    (hdiag : ∀ i, κ * E i ≤ -(Bre i i))
    (hres : ∀ i j, i ≠ j → ¬ LF i j → Bre i j ≤ residual i j * (E i + E j))
    (hrow : ∀ i, (∑ j ∈ univ.erase i, (if LF i j then c else residual i j)) ≤ β) :
    (∑ i, ∑ j, Bre i j) ≤
      -(κ - 2 * β) * (∑ i, E i)
        - ∑ i, ∑ j ∈ univ.erase i, (if LF i j then c * (E i + E j) - Bre i j else 0) := by
  obtain ⟨cost, hcost⟩ : ∃ cost : ι → ι → ℝ,
      ∀ i j, cost i j = if LF i j then c else residual i j := ⟨_, fun _ _ => rfl⟩
  have hrow' : ∀ i, ∑ j ∈ univ.erase i, cost i j ≤ β := by
    intro i
    simpa only [hcost] using hrow i
  have hcsymm : ∀ i j, cost i j = cost j i := by
    intro i j
    rw [hcost i j, hcost j i]
    by_cases h : LF i j
    · rw [if_pos h, if_pos ((hLF i j).mp h)]
    · rw [if_neg h, if_neg (fun hji => h ((hLF i j).mpr hji))]
      exact hrsymm i j
  have hA : ∑ i, E i * ∑ j ∈ univ.erase i, cost i j ≤ β * ∑ i, E i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [mul_comm β (E i)]
    exact mul_le_mul_of_nonneg_left (hrow' i) (hE i)
  have hR1 : ∑ i, E i * ∑ j ∈ univ.erase i, cost i j
      = ∑ i, ∑ j ∈ univ.erase i, E i * cost i j :=
    Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
  have hR2 : ∑ i, ∑ j ∈ univ.erase i, E i * cost i j
      = ∑ i, ∑ j ∈ univ.erase i, E j * cost i j := by
    have hsw := offdiag_swap (fun i j => E i * cost i j)
    beta_reduce at hsw
    rw [hsw]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [hcsymm j i]
  have hsum : ∑ i, ∑ j ∈ univ.erase i, (E i + E j) * cost i j
      = (∑ i, ∑ j ∈ univ.erase i, E i * cost i j)
        + ∑ i, ∑ j ∈ univ.erase i, E j * cost i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h2R : ∑ i, ∑ j ∈ univ.erase i, (E i + E j) * cost i j
      = 2 * ∑ i, E i * ∑ j ∈ univ.erase i, cost i j := by
    rw [hsum, ← hR2, ← hR1]
    ring
  have hC : ∑ i, ∑ j ∈ univ.erase i,
        ((if LF i j then c * (E i + E j) - Bre i j else 0) + Bre i j)
      ≤ ∑ i, ∑ j ∈ univ.erase i, (E i + E j) * cost i j := by
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j hj => ?_))
    have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    rw [hcost i j]
    by_cases h : LF i j
    · simp only [if_pos h]
      exact (by ring : c * (E i + E j) - Bre i j + Bre i j = (E i + E j) * c).le
    · simp only [if_neg h]
      rw [zero_add, mul_comm]
      exact hres i j hne h
  have hD : κ * (∑ i, E i) ≤ -(∑ i, Bre i i) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i _ => hdiag i)
  have hsplit : ∑ i, ∑ j ∈ univ.erase i,
        ((if LF i j then c * (E i + E j) - Bre i j else 0) + Bre i j)
      = (∑ i, ∑ j ∈ univ.erase i, (if LF i j then c * (E i + E j) - Bre i j else 0))
        + ((∑ i, ∑ j, Bre i j) - ∑ i, Bre i i) := by
    rw [← offdiag_eq Bre, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib)
  have key : (∑ i, ∑ j, Bre i j) ≤
      2 * (β * ∑ i, E i) - κ * (∑ i, E i)
        - ∑ i, ∑ j ∈ univ.erase i, (if LF i j then c * (E i + E j) - Bre i j else 0) := by
    linarith [hA, h2R, hC, hD, hsplit]
  have e : -(κ - 2 * β) * (∑ i, E i) = 2 * (β * ∑ i, E i) - κ * (∑ i, E i) := by ring
  rw [e]
  exact key

/-- The constants of `hresidual`: diagonal `5671/3200`, row budget `57430/65536`.
    The exact difference is `8013/409600`; `641/32768` is a lower bound for it. -/
theorem hresidual_constants :
    (5671 / 3200 : ℝ) - 2 * (57430 / 65536) = 8013 / 409600 ∧
      (641 / 32768 : ℝ) ≤ 8013 / 409600 := by
  constructor <;> norm_num

end AEGIS.RHResonanceRowWeightedSumV1

#print axioms AEGIS.RHResonanceRowWeightedSumV1.weighted_row_sum
