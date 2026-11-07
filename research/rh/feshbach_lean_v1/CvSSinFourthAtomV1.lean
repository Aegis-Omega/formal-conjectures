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

import CvSAtomInversionV1
import Mathlib.Tactic

/-!
# CvS sin-fourth stencil, exact old-atom decomposition

An algebraic component of OPTIMUS V9/V10. The three existing sin-squared
atoms at frequencies n-1, n and n+1 produce the five-source-mode stencil
of (d²/dx² - 1/4)(sin⁴(pi*x/L) * exp(2*pi*i*n*x/L)).

The analytic H¹-density theorem and the global Weil sign are NOT proved here.
This file is a source candidate until compiled by the pinned Lean 4.33.1 kernel.
-/

open Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.CvSSinFourthAtomV1

open AEGIS.CvSAtomInversionV1
open AEGIS.CvSMomentBasisV1

/-- A `sin⁴` source expressed using *only* existing `momentAtom` sources. -/
def sinFourthAtom (L : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  -(1 / 4) * momentAtom L (n - 1) x +
    (1 / 2) * momentAtom L n x -
      (1 / 4) * momentAtom L (n + 1) x

/-- The exact five Fourier coefficients of the sin-fourth source.
No truncation, Gram inversion, determinant, or certificate is used. -/
theorem sinFourthAtom_eq_fiveEz (L : ℝ) (n : ℤ) (x : ℝ) :
    sinFourthAtom L n x =
      (1 / 16) * Ez L (n - 2) x -
      (1 / 4) * Ez L (n - 1) x +
      (3 / 8) * Ez L n x -
      (1 / 4) * Ez L (n + 1) x +
      (1 / 16) * Ez L (n + 2) x := by
  unfold sinFourthAtom
  rw [momentAtom_eq L (n - 1) x, momentAtom_eq L n x,
    momentAtom_eq L (n + 1) x]
  have h1 : n - 1 - 1 = n - 2 := by omega
  have h2 : n - 1 + 1 = n := by omega
  have h3 : n + 1 - 1 = n := by omega
  have h4 : n + 1 + 1 = n + 2 := by omega
  rw [h1, h2, h3, h4]
  ring

/-- Zeroth discrete moment of the exact five-mode potential stencil. -/
theorem fiveStencil_sum_zero :
    (1 / 16 : ℂ) - 1 / 4 + 3 / 8 - 1 / 4 + 1 / 16 = 0 := by
  norm_num

/-- First discrete moment of the exact five-mode potential stencil. -/
theorem fiveStencil_firstMoment_zero (n : ℤ) :
    (1 / 16 : ℂ) * (((n - 2 : ℤ) : ℂ)) -
    (1 / 4 : ℂ) * (((n - 1 : ℤ) : ℂ)) +
    (3 / 8 : ℂ) * (n : ℂ) -
    (1 / 4 : ℂ) * (((n + 1 : ℤ) : ℂ)) +
    (1 / 16 : ℂ) * (((n + 2 : ℤ) : ℂ)) = 0 := by
  push_cast
  ring

end AEGIS.CvSSinFourthAtomV1

#print axioms AEGIS.CvSSinFourthAtomV1.sinFourthAtom_eq_fiveEz
#print axioms AEGIS.CvSSinFourthAtomV1.fiveStencil_sum_zero
#print axioms AEGIS.CvSSinFourthAtomV1.fiveStencil_firstMoment_zero
