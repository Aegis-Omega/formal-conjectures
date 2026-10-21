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

import CvSLowCoercivityL12V1

/-!
# Schur closure with a row budget relative to the low form

`hlow_of_coercivity_and_budget` compares the row budget with `‖c‖²`. At L = 6/5 the low form
`Q_CvS` has condition number about `2·10¹²` in the atom coordinates, so that comparison needs a
Schur gap of order `10¹²`. Here the budget is compared with `Q_CvS` itself: `Brow c ≤ κ Q(c)` and
`κ ≤ (2π)² LT (m − T/(2π))` give the same `hlow` conclusion. Not RH.
-/

open AEGIS.CvSSchurClosureFromBoundsV1 AEGIS.CvSProjectedPackedCertificateL12V1

namespace AEGIS.CvSRelativeBudgetL12V1

/-- `hlow` from a budget measured against the low form. -/
theorem hlow_of_relative_budget {p : ℕ} (LT m T_trace kappa : ℝ)
    (Q_form B : (Fin p → ℂ) → ℝ) (hLT : 0 < LT) (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hQ : ∀ c, 0 ≤ Q_form c) (hB : ∀ c, B c ≤ kappa * Q_form c)
    (hk : kappa ≤ (2 * Real.pi) ^ 2 * LT * (m - T_trace / (2 * Real.pi))) :
    ∀ c, B c / (2 * Real.pi * LT) / (m - T_trace / (2 * Real.pi)) ≤ 2 * Real.pi * Q_form c := by
  intro c
  set g := m - T_trace / (2 * Real.pi)
  have hden : 0 < 2 * Real.pi * LT := by positivity
  have h1 : B c ≤ (2 * Real.pi) ^ 2 * LT * g * Q_form c :=
    (hB c).trans (mul_le_mul_of_nonneg_right hk (hQ c))
  rw [div_div, div_le_iff₀ (mul_pos hden hgap)]
  calc B c ≤ (2 * Real.pi) ^ 2 * LT * g * Q_form c := h1
    _ = 2 * Real.pi * Q_form c * (2 * Real.pi * LT * g) := by ring

/-- The low form at L = 6/5 is nonnegative. -/
theorem Q_nonneg_L12 (M : ℕ) (hM : 3 ≤ M) (c : Fin 139 → ℂ) :
    0 ≤ Q_CvS M (6 / 5) atomCenter c := by
  have h := AEGIS.CvSLowCoercivityL12V1.original_atom_coercivity_L12 M hM c
  have hn : 0 ≤ normSqCoeffs c := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact le_trans (mul_nonneg AEGIS.CvSLowCoercivityL12V1.coercivity_const_pos.le hn) h

/-- The L = 6/5 low-block consumer with a budget relative to `Q_CvS`. -/
theorem hlow_L12_relative (M : ℕ) (hM : 3 ≤ M) (m T_trace kappa : ℝ)
    (Brow : (Fin 139 → ℂ) → ℝ) (hgap : 0 < m - T_trace / (2 * Real.pi))
    (hB : ∀ c, Brow c ≤ kappa * Q_CvS M (6 / 5) atomCenter c)
    (hk : kappa ≤ (2 * Real.pi) ^ 2 * (6 / 5 : ℝ) * (m - T_trace / (2 * Real.pi))) :
    ∀ c, Brow c / (2 * Real.pi * (6 / 5 : ℝ)) / (m - T_trace / (2 * Real.pi)) ≤
      2 * Real.pi * Q_CvS M (6 / 5) atomCenter c :=
  hlow_of_relative_budget (6 / 5) m T_trace kappa (Q_CvS M (6 / 5) atomCenter) Brow
    (by norm_num) hgap (Q_nonneg_L12 M hM) hB hk

end AEGIS.CvSRelativeBudgetL12V1

#print axioms AEGIS.CvSRelativeBudgetL12V1.hlow_of_relative_budget
#print axioms AEGIS.CvSRelativeBudgetL12V1.Q_nonneg_L12
#print axioms AEGIS.CvSRelativeBudgetL12V1.hlow_L12_relative
