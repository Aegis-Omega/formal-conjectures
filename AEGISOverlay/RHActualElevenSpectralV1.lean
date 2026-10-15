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

import AEGISOverlay.RHActualElevenLatticeV1

/-!
# Exact eleven-block reflected spectral arithmetic

The source-derived Q16.16 **absolute mixed-cost matrix** is a real symmetric
nonnegative matrix after scaling by 1/65536. It is NOT the Weil Gram itself.
The integer cost matrix has an invariant 3-dimensional reflected-even block,
an invariant 2-dimensional reflected-odd block, and six eigenvectors with
eigenvalue -656. All action identities and the integer lower witness below
are exact and kernel-checkable.

The previously proved weighted-Schur certificate bounds its largest
eigenvalue by 46688. The explicit integral Rayleigh witness rules out
every smaller *integer* bound. None of these claims gives a universal RH
mixed-term certificate for arbitrary moment-zero packets.
-/

open scoped BigOperators
set_option autoImplicit false

namespace AEGIS.RHActualElevenSpectralV1

open AEGIS.RHActualElevenLatticeV1

/-- Numerators of the source-derived absolute Q16.16 mixed costs. -/
def C (i j : Fin 11) : ℤ := (elevenCostUnits i j : ℤ)

def action (v : Fin 11 → ℤ) (i : Fin 11) : ℤ :=
  ∑ j : Fin 11, C i j * v j

def reflect (i : Fin 11) : Fin 11 :=
  ⟨10 - i.val, by omega⟩

theorem cost_reflect (i j : Fin 11) :
    C (reflect i) (reflect j) = C i j := by
  fin_cases i <;> fin_cases j <;> decide

def evenZero (i : Fin 11) : ℤ :=
  if i = 0 ∨ i = 10 then 1 else 0

def evenOne (i : Fin 11) : ℤ :=
  if i = 1 ∨ i = 9 then 1 else 0

def evenMiddle (i : Fin 11) : ℤ :=
  if 2 ≤ i.val ∧ i.val ≤ 8 then 1 else 0

def oddZero (i : Fin 11) : ℤ :=
  if i = 0 then 1 else if i = 10 then -1 else 0

def oddOne (i : Fin 11) : ℤ :=
  if i = 1 then 1 else if i = 9 then -1 else 0

/-- Six independent central differences, supported on indices 2 through 8. -/
def middleDifference (k : Fin 6) (i : Fin 11) : ℤ :=
  if i.val = k.val + 2 then 1 else if i = 8 then -1 else 0

/-- Columns of the even invariant block:
    [[14826,38012,4592],[38012,656,4592],[1312,1312,3936]]. -/
theorem even_zero_action (i : Fin 11) :
    action evenZero i =
      14826 * evenZero i + 38012 * evenOne i + 1312 * evenMiddle i := by
  fin_cases i <;> decide

theorem even_one_action (i : Fin 11) :
    action evenOne i =
      38012 * evenZero i + 656 * evenOne i + 1312 * evenMiddle i := by
  fin_cases i <;> decide

theorem even_middle_action (i : Fin 11) :
    action evenMiddle i =
      4592 * evenZero i + 4592 * evenOne i + 3936 * evenMiddle i := by
  fin_cases i <;> decide

/-- Odd invariant block [[-14826,-36700],[-36700,-656]]. -/
theorem odd_zero_action (i : Fin 11) :
    action oddZero i = -14826 * oddZero i - 36700 * oddOne i := by
  fin_cases i <;> decide

theorem odd_one_action (i : Fin 11) :
    action oddOne i = -36700 * oddZero i - 656 * oddOne i := by
  fin_cases i <;> decide

/-- The six central difference directions each have eigenvalue -656. -/
theorem middle_difference_eigen (k : Fin 6) (i : Fin 11) :
    action (middleDifference k) i = -656 * middleDifference k i := by
  fin_cases k <;> fin_cases i <;> decide

/-- The exact positive Perron-style witness already present in PR #88. -/
def witness (i : Fin 11) : ℤ := (elevenOptimizedWeightUnits i : ℤ)

theorem witness_norm_exact :
    (∑ i : Fin 11, witness i * witness i) = 620740 := by
  decide

theorem witness_cost_quadratic_exact :
    (∑ i : Fin 11, ∑ j : Fin 11, witness i * C i j * witness j) =
      28980560964 := by
  decide

/-- Rational Rayleigh quotient exceeds 46687/65536, not an approximation. -/
theorem rayleigh_gt_46687 :
    46687 * (∑ i : Fin 11, witness i * witness i) <
      (∑ i : Fin 11, ∑ j : Fin 11, witness i * C i j * witness j) := by
  rw [witness_norm_exact, witness_cost_quadratic_exact]
  norm_num

/-- Since a single integral vector rules out 46687, the existing
    46688 weighted-Schur row certificate is integer-scale optimal. -/
theorem no_smaller_integral_quadratic_bound (S : ℤ)
    (h : ∀ v : Fin 11 → ℤ,
      (∑ i : Fin 11, ∑ j : Fin 11, v i * C i j * v j) ≤
        S * (∑ i : Fin 11, v i * v i)) :
    46688 ≤ S := by
  have hw := h witness
  rw [witness_cost_quadratic_exact, witness_norm_exact] at hw
  omega

end AEGIS.RHActualElevenSpectralV1

#print axioms AEGIS.RHActualElevenSpectralV1.cost_reflect
#print axioms AEGIS.RHActualElevenSpectralV1.even_zero_action
#print axioms AEGIS.RHActualElevenSpectralV1.even_one_action
#print axioms AEGIS.RHActualElevenSpectralV1.even_middle_action
#print axioms AEGIS.RHActualElevenSpectralV1.odd_zero_action
#print axioms AEGIS.RHActualElevenSpectralV1.odd_one_action
#print axioms AEGIS.RHActualElevenSpectralV1.middle_difference_eigen
#print axioms AEGIS.RHActualElevenSpectralV1.witness_norm_exact
#print axioms AEGIS.RHActualElevenSpectralV1.witness_cost_quadratic_exact
#print axioms AEGIS.RHActualElevenSpectralV1.rayleigh_gt_46687
#print axioms AEGIS.RHActualElevenSpectralV1.no_smaller_integral_quadratic_bound
