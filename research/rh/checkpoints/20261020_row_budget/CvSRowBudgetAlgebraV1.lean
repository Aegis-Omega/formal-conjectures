/- Finite Gram identities for the signed relative CvS row budget. -/
import CvSFiniteCongruenceV1
import Mathlib.Analysis.Complex.Norm

open scoped BigOperators ComplexConjugate
namespace AEGIS.CvSRowBudgetAlgebraV1

/-- A real finite residual matrix has exactly its Gram quadratic energy. -/
theorem row_energy_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : κ → ι → ℝ) (v : ι → ℂ) :
    (∑ k, ‖∑ i, (R k i : ℂ) * v i‖ ^ 2) =
      (∑ i, ∑ j, v i * conj (v j) * ((∑ k, R k i * R k j : ℝ) : ℂ)).re := by
  classical
  have h := AEGIS.CvSFiniteCongruenceV1.quadratic_form_real_congruence
    (fun k l : κ => if k = l then (1 : ℝ) else 0) R v
  simpa [mul_ite, Complex.re_sum, Complex.mul_conj, Complex.sq_norm, Complex.normSq_apply] using
    (congrArg Complex.re h).symm

end AEGIS.CvSRowBudgetAlgebraV1
#print axioms AEGIS.CvSRowBudgetAlgebraV1.row_energy_eq
