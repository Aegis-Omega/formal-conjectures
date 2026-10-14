/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.

AEGIS Omega: source-only two-scale actual Weil row-budget bridge.
This imports the existing genuine-Weil signed-row consumer on PR #88.
The near/far inequalities are EXPLICIT hypotheses: no analytic bound
on the prime part or unconditional RH is claimed.
-/
import AEGISOverlay.RHActualUniversalFineGramV1

open Finset
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHScaleRowCompositionV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.RHGramExpansionV13
open AEGIS.RHActualUniversalFineGramV1

/-- An arbitrary assignment of actual fine packets to macro blocks splits
    the entire off-diagonal row into same-block and cross-block terms.
    No entry is discarded, even if it is signed or negative. -/
theorem actual_row_eq_near_add_far
    {n : ℕ} (block : Fin (n + 1) → ℕ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, c i j) =
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then c i j else 0) +
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then c i j else 0) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : block i = block j
  · simp [h]
  · simp [h]

/-- A two-scale allocation implies the single actual row budget.
    There is no cardinality-dependent per-pair rounding. -/
theorem actual_row_le_of_near_far
    {n : ℕ} (block : Fin (n + 1) → ℕ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (near far : ℝ)
    (hnear : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then c i j else 0) ≤ near)
    (hfar : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then c i j else 0) ≤ far) :
    ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        c i j) ≤ near + far := by
  intro i
  rw [actual_row_eq_near_add_far block c i]
  exact add_le_add (hnear i) (hfar i)

/-- The existing real-signed actual-Weil coercivity theorem is inherited
    from two *separately certified* scales. In particular, a verified
    near/far budget is not merely a toy Gram surrogate: the conclusion
    is the original arithmetic Weil B for the recomposed packet. -/
theorem actual_weil_coercive_of_two_scale_signed_rows
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (block : Fin (n + 1) → ℕ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (near far : ℝ)
    (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, (5671 / 3200 : ℝ) * energy (gs i).1 ≤
      -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1))
    (hnear : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i = block j then c i j else 0) ≤ near)
    (hfar : ∀ i : Fin (n + 1),
      (∑ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        if block i ≠ block j then c i j else 0) ≤ far)
    (hbudget : near + far ≤ (57430 / 65536 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
      (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
        -(641 / 32768 : ℝ) * (∑ i, energy (gs i).1) := by
  apply actual_fine_gram_coercive_of_signed_real_row_certificate
    gs c hsym hdiag hcross
  intro i
  exact (actual_row_le_of_near_far block c near far hnear hfar i).trans hbudget

/-- Exact Q16.16 arithmetical allocation: splitting 57430 units over
    the two scales cannot exceed the budget. -/
theorem q16_two_scale_units
    (nearUnits farUnits : ℕ)
    (h : nearUnits + farUnits ≤ 57430) :
    (nearUnits : ℝ) / 65536 + (farUnits : ℝ) / 65536 ≤
      (57430 / 65536 : ℝ) := by
  have hh : ((nearUnits + farUnits : ℕ) : ℝ) ≤ (57430 : ℝ) := by
    exact_mod_cast h
  norm_num at hh ⊢
  linarith

end AEGIS.RHScaleRowCompositionV1

#print axioms AEGIS.RHScaleRowCompositionV1.actual_row_eq_near_add_far
#print axioms AEGIS.RHScaleRowCompositionV1.actual_row_le_of_near_far
#print axioms AEGIS.RHScaleRowCompositionV1.actual_weil_coercive_of_two_scale_signed_rows
#print axioms AEGIS.RHScaleRowCompositionV1.q16_two_scale_units
