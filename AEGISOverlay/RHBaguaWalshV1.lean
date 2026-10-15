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

/-!
# AEGIS Ω — exact Bagua eight-trigram Walsh arithmetic

The eight yin/yang trigrams are the three binary digits of Fin 8.
For a,b ∈ F₂³, the Walsh kernel H(a,b)=(-1)^(a·b) has only integer
entries ±1. We prove H² = 8I by exhaustive kernel-reducible checks.

Therefore the inverse is H/8. The rational factors 1/8 and 1/64
have exact Q16.16 numerators 8192 and 1024. Fu Xi and King Wen
arrangements permute these eight states.

This module makes NO claim that the actual Weil Gram is xor-circulant
or that a change of basis proves an unknown global sign. -/

open scoped BigOperators

namespace AEGIS.RHBaguaWalshV1

/-- Binary dot-product parity of three line bits. -/
private def bitDotParity (a b : Fin 8) : Nat :=
  ((a.val % 2) * (b.val % 2) +
    ((a.val / 2) % 2) * ((b.val / 2) % 2) +
    ((a.val / 4) % 2) * ((b.val / 4) % 2)) % 2

/-- Exact 8×8 integer Walsh matrix entry. -/
def walsh8 (a b : Fin 8) : ℤ :=
  if bitDotParity a b = 0 then 1 else -1

theorem walsh8_symmetric (a b : Fin 8) :
    walsh8 a b = walsh8 b a := by
  fin_cases a <;> fin_cases b <;> decide

/-- Character orthogonality; all 64 entries certified exactly. -/
theorem walsh8_row_orthogonality (a b : Fin 8) :
    (∑ x : Fin 8, walsh8 a x * walsh8 b x) =
      if a = b then (8 : ℤ) else 0 := by
  fin_cases a <;> fin_cases b <;> decide

/-- Entrywise exact identity H₈² = 8I. -/
theorem walsh8_square (a b : Fin 8) :
    (∑ x : Fin 8, walsh8 a x * walsh8 x b) =
      if a = b then (8 : ℤ) else 0 := by
  fin_cases a <;> fin_cases b <;> decide

/-- H₈⁻¹ = H₈/8 uses 8192 units of Q16.16. -/
theorem walsh8_inverse_q16_exact :
    (8192 : ℤ) * 8 = 65536 := by
  norm_num

/-- Double congruence H₈ G H₈ /64 uses 1024 Q16.16 units. -/
theorem walsh8_double_congruence_q16_exact :
    (1024 : ℤ) * 64 = 65536 := by
  norm_num

end AEGIS.RHBaguaWalshV1

#print axioms AEGIS.RHBaguaWalshV1.walsh8_symmetric
#print axioms AEGIS.RHBaguaWalshV1.walsh8_row_orthogonality
#print axioms AEGIS.RHBaguaWalshV1.walsh8_square
#print axioms AEGIS.RHBaguaWalshV1.walsh8_inverse_q16_exact
#print axioms AEGIS.RHBaguaWalshV1.walsh8_double_congruence_q16_exact
