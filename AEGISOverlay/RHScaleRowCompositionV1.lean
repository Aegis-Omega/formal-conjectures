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


import AEGISOverlay.RHActualUniversalFineGramV1

/-!
AEGIS Omega: source-only two-scale actual Weil row-budget bridge.
This imports the existing genuine-Weil signed-row consumer on PR #88.
The near/far inequalities are EXPLICIT hypotheses: no analytic bound
on the prime part or unconditional RH is claimed.
-/

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


/-! ## Coarse scale: exact local 9/64 control pays for every near interaction

Each macro packet may itself be the sum of arbitrarily many moment-zero
fine atoms. Its genuine diagonal is controlled by the existing local
nine-over-64 analytic theorem, not by an entrywise near-pair bound.
Only the cross-MACRO signed row remains a hypothesis. -/

/-- Coarse Weil packets each occupy their own 9/64 logarithmic window.
The actual local signed Gram is paid exactly. A signed cross-macro row
budget 2 * R + gap <= 1/10 then yields a quantitative global sign.
No cross-macro analytic estimate or universal producer is assumed. -/
theorem actual_nine_macro_coercive_of_signed_cross_rows
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (R gap : ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (9 / 64) (center i))
    (hsym : ∀ i j, c i j = c j i)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      c i j) ≤ R)
    (hbudget : 2 * R + gap ≤ (1 / 10 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤
      -gap * (∑ i, energy (gs i).1) := by
  have hd (i : Fin (n + 1)) :
      (1 / 10 : ℝ) * energy (gs i).1 ≤
        -(B (gs i) (gs i)).re := by
    have h := AEGIS.RHWindowNineOver64GlobalizationV14.nine_over_64_coercive
      (gs i) (center i) (hwin i) (hm i)
    change (B (gs i) (gs i)).re ≤
      -(1 / 10 : ℝ) * energy (gs i).1 at h
    linarith
  have hs :
      (∑ i, (1 / 10 : ℝ) * energy (gs i).1) ≤
      ∑ i, -(B (gs i) (gs i)).re :=
    Finset.sum_le_sum (fun i _ => hd i)
  have hdiag :
      (1 / 10 : ℝ) * (∑ i, energy (gs i).1) ≤
        -(∑ i, (B (gs i) (gs i)).re) := by
    rw [Finset.mul_sum]
    simpa only [Finset.sum_neg_distrib] using hs
  have hmixed := actual_mixed_defect_le_of_signed_symmetric_row
    gs c R hsym hcross hrow
  have hgram :
      (B (packetSum (fun _ => (1 : ℂ)) gs)
         (packetSum (fun _ => (1 : ℂ)) gs)).re =
        (∑ i, ∑ j, B (gs i) (gs j)).re := by
    rw [B_packetSum]
    simp
  rw [← hgram] at hmixed
  unfold AEGIS.RHActualMixedDefectV1.actualMixedDefect at hmixed
  have hE : 0 ≤ (∑ i, energy (gs i).1) :=
    Finset.sum_nonneg (fun i _ => energy_nonnegative (gs i).1)
  have hbudgetE :
      (2 * R + gap) * (∑ i, energy (gs i).1) ≤
      (1 / 10 : ℝ) * (∑ i, energy (gs i).1) :=
    mul_le_mul_of_nonneg_right hbudget hE
  nlinarith

/-- Non-strict full global sign under the concrete macro row threshold 1/20. -/
theorem actual_nine_macro_nonpositive_of_signed_cross_rows
    {n : ℕ} (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (center : Fin (n + 1) → ℝ)
    (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hm : ∀ i, WeilMomentConditionsV1 (gs i))
    (hwin : ∀ i, AEGIS.RHDyadicDiagonalV13.HalfWidthAt
      (gs i) (9 / 64) (center i))
    (hsym : ∀ i j, c i j = c j i)
    (hcross : ∀ i j, i ≠ j →
      (B (gs i) (gs j)).re ≤
        c i j * (energy (gs i).1 + energy (gs j).1))
    (hrow : ∀ i, (∑ j ∈
      (Finset.univ : Finset (Fin (n + 1))).erase i,
      c i j) ≤ (1 / 20 : ℝ)) :
    (B (packetSum (fun _ => (1 : ℂ)) gs)
       (packetSum (fun _ => (1 : ℂ)) gs)).re ≤ 0 := by
  have h := actual_nine_macro_coercive_of_signed_cross_rows
    gs center c (1 / 20 : ℝ) 0 hm hwin hsym hcross hrow (by norm_num)
  simpa using h

end AEGIS.RHScaleRowCompositionV1

#print axioms AEGIS.RHScaleRowCompositionV1.actual_row_eq_near_add_far
#print axioms AEGIS.RHScaleRowCompositionV1.actual_row_le_of_near_far
#print axioms AEGIS.RHScaleRowCompositionV1.actual_weil_coercive_of_two_scale_signed_rows
#print axioms AEGIS.RHScaleRowCompositionV1.q16_two_scale_units

#print axioms AEGIS.RHScaleRowCompositionV1.actual_nine_macro_coercive_of_signed_cross_rows
#print axioms AEGIS.RHScaleRowCompositionV1.actual_nine_macro_nonpositive_of_signed_cross_rows
